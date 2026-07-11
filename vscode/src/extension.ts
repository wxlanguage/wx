import * as fs from "node:fs";
import * as path from "node:path";
import * as process from "node:process";
import {
	workspace,
	ExtensionContext,
	ExtensionMode,
	commands,
	window,
	Uri,
	FileSystemWatcher,
	EventEmitter,
	TextDocument,
} from "vscode";
import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
} from "vscode-languageclient/node";
import {
	AnsiDecorationProvider,
	DIAGNOSTICS_VIEW_SCHEME,
	stripAnsi,
} from "./ansiDecorations";

let client: LanguageClient | null = null;

function fileExists(filePath: string): boolean {
	try {
		return fs.statSync(filePath).isFile();
	} catch {
		return false;
	}
}

function splitPathEnvValue(value: string): string[] {
	const separator = process.platform === "win32" ? ";" : ":";
	return value
		.split(separator)
		.map((entry) => entry.trim())
		.filter((entry) => entry.length > 0);
}

// On Windows, `wx` on PATH may be `wx.exe`, `wx.cmd` (an npm global-install
// shim), etc. — `PATHEXT` lists which suffixes actually count as executable.
function candidateNames(baseName: string): string[] {
	if (process.platform !== "win32") return [baseName];
	const pathExt = process.env.PATHEXT ?? ".EXE;.CMD;.BAT;.COM";
	return splitPathEnvValue(pathExt).map((ext) => baseName + ext);
}

// Manually walks `PATH` looking for a `wx` executable — the same resolution
// `child_process.spawn("wx", ...)` does internally, just done eagerly so we
// can show a specific, actionable error message ahead of time instead of
// waiting for `client.start()` to fail with a generic "spawn wx ENOENT".
// Mirrors `getDefaultDenoCommand` in denoland/vscode_deno's
// client/src/util.ts.
function findWxOnPath(): string | undefined {
	const pathValue = process.env.PATH ?? "";
	for (const dir of splitPathEnvValue(pathValue)) {
		for (const name of candidateNames("wx")) {
			const candidate = path.join(dir, name);
			if (fileExists(candidate)) return candidate;
		}
	}
	return undefined;
}

// Resolved fresh on every start/restart (not cached) so that changing
// `wx.path` and running "WX: Restart Language Server" picks it up without a
// full window reload. Returns `undefined` if nothing resolvable was found,
// so `startServer` can show a specific error instead of letting
// `client.start()` fail with an opaque one.
const resolveServerCommand = (
	context: ExtensionContext,
): string | undefined => {
	const configured = workspace.getConfiguration("wx").get<string>("path");
	if (configured) {
		const resolved = path.isAbsolute(configured)
			? configured
			: (workspace.workspaceFolders?.[0] &&
				path.resolve(workspace.workspaceFolders[0].uri.fsPath, configured));
		return resolved && fileExists(resolved) ? resolved : undefined;
	}

	if (context.extensionMode === ExtensionMode.Development) {
		const devBinary = path.resolve(
			context.extensionPath,
			"..",
			"target",
			"debug",
			process.platform === "win32" ? "wx.exe" : "wx",
		);
		if (fileExists(devBinary)) return devBinary;
	}

	// No bundled binary (unlike the old per-platform .vsix builds) — same
	// model as `deno.path`: resolve `wx` from the user's PATH.
	return findWxOnPath();
};

let fileWatcher: FileSystemWatcher | null = null;

// Fired with a `wx-diagnostics-view` URI whenever the diagnostic behind it
// gets republished, so an already-open virtual doc for that URI re-fetches
// instead of showing whatever was cached the first time it was opened —
// otherwise editing a file that shuffles diagnostics around leaves a stale
// open tab pointed at old content forever, since VS Code only re-invokes
// `provideTextDocumentContent` for a URI already backing an open document
// when told to via this event (a no-op if nothing has it open).
const diagnosticsViewChanged = new EventEmitter<Uri>();

// Re-parses the same raw ANSI text `wx/fullDiagnostic` returns (the content
// provider below strips it for the document's plain text) into
// `TextEditorDecorationType`s, so a "click for full compiler diagnostic"
// view is colored the same way `wx-cli` colors it in a real terminal.
const decorationProvider = new AnsiDecorationProvider(async (uri) => {
	if (!client) return null;
	return client.sendRequest<string>("wx/fullDiagnostic", {
		uri: uri.fragment,
		index: Number(uri.query),
	});
});

async function decorateVisibleEditors(document: TextDocument) {
	for (const editor of window.visibleTextEditors) {
		if (editor.document === document) {
			await decorationProvider.provideDecorations(editor);
		}
	}
}

async function startServer(context: ExtensionContext) {
	const serverCommand = resolveServerCommand(context);
	if (!serverCommand) {
		const configured = workspace.getConfiguration("wx").get<string>("path");
		const message = configured
			? `Could not find the 'wx' executable at the configured "wx.path": ${configured}`
			: "Could not find the 'wx' executable on your PATH. Install it " +
				"with `npm install -g @wx-lang/cli` (or `cargo install --path " +
				'crates/wx-cli`), or set the "wx.path" setting to point to it directly.';
		const action = await window.showErrorMessage(message, "Open Settings");
		if (action === "Open Settings") {
			commands.executeCommand(
				"workbench.action.openSettings",
				"wx.path",
			);
		}
		return;
	}

	// No `transport` here: for an `Executable`, vscode-languageclient treats
	// an explicit `TransportKind.stdio` as a signal to append a `--stdio`
	// flag to `args` (the convention some LSP servers use to pick their
	// transport) — `wx lsp` always talks over stdio and doesn't accept that
	// flag, so it'd reject it (`error: unexpected argument '--stdio' found`).
	// Omitting `transport` spawns/pipes identically but skips that flag.
	const serverOptions: ServerOptions = {
		command: serverCommand,
		args: ["lsp"],
	};

	fileWatcher?.dispose();
	fileWatcher = workspace.createFileSystemWatcher("**/*.wx");

	const clientOptions: LanguageClientOptions = {
		documentSelector: [
			{ scheme: "file", language: "wx" },
			{ scheme: "wx", language: "wx" },
		],
		synchronize: {
			fileEvents: fileWatcher,
		},
		outputChannelName: "WX Language Server",
		middleware: {
			handleDiagnostics(uri, diagnosticList, next) {
				diagnosticList.forEach((diag, idx) => {
					if (diag.source !== "wx" || !diag.code) return;
					const target = Uri.from({
						scheme: DIAGNOSTICS_VIEW_SCHEME,
						path: `/diagnostic-${idx}`,
						fragment: uri.toString(),
						query: idx.toString(),
					});
					diag.code = {
						target,
						value: typeof diag.code === "object" ? diag.code.value : diag.code,
					};
					// No-op if this URI isn't currently backing an open
					// document; otherwise makes an already-open virtual doc
					// re-fetch instead of staying pinned to stale content.
					diagnosticsViewChanged.fire(target);
				});
				next(uri, diagnosticList);
			},
		},
	};

	client = new LanguageClient(
		"wx-lsp",
		"WX Language Server",
		serverOptions,
		clientOptions,
	);

	try {
		await client.start();
	} catch (error) {
		const action = await window.showErrorMessage(
			`Failed to start WX Language Server: ${error}`,
			"Open Output",
		);
		if (action === "Open Output") {
			client.outputChannel.show();
		}
	}
}

export function activate(context: ExtensionContext) {
	const restartCommand = commands.registerCommand(
		"wx-vscode.restartServer",
		async () => {
			window.showInformationMessage("Restarting WX Language Server...");

			if (client) {
				await client.stop();
			}

			await startServer(context);
		},
	);

	const configListener = workspace.onDidChangeConfiguration((e) => {
		if (e.affectsConfiguration("wx")) {
			commands.executeCommand("wx-vscode.restartServer");
		}
	});

	context.subscriptions.push(restartCommand, configListener);
	startServer(context);

	// Provide content for wx:// virtual stdlib URIs (e.g. wx://std/lib.wx)
	context.subscriptions.push(
		workspace.registerTextDocumentContentProvider("wx", {
			provideTextDocumentContent: (uri: Uri) => {
				if (!client) return null;
				return client.sendRequest("wx/virtualFileContent", {
					uri: uri.toString(),
				});
			},
		}),
	);

	// Provide the full rendered diagnostic text for the "Click for full
	// compiler diagnostic" links installed by the handleDiagnostics
	// middleware above. The document's own text is plain (ANSI codes
	// stripped) — coloring is applied separately as decorations, since VS
	// Code can't render ANSI escapes in a regular editor buffer.
	context.subscriptions.push(
		diagnosticsViewChanged,
		workspace.registerTextDocumentContentProvider(DIAGNOSTICS_VIEW_SCHEME, {
			onDidChange: diagnosticsViewChanged.event,
			provideTextDocumentContent: async (uri: Uri) => {
				if (!client) return null;
				const raw = await client.sendRequest<string>("wx/fullDiagnostic", {
					uri: uri.fragment,
					index: Number(uri.query),
				});
				return stripAnsi(raw);
			},
		}),
	);

	// Filtered to `DIAGNOSTICS_VIEW_SCHEME` right here, before touching
	// `visibleTextEditors` or awaiting anything — these first two fire on
	// every edit/open of *any* document in the editor, not just diagnostics
	// views, so bailing a line earlier than `provideDecorations` would
	// anyway matters here in a way it doesn't for the other two (which only
	// fire on tab/visibility changes, not per keystroke).
	context.subscriptions.push(
		decorationProvider,
		workspace.onDidChangeTextDocument((event) => {
			if (event.document.uri.scheme !== DIAGNOSTICS_VIEW_SCHEME) return;
			decorateVisibleEditors(event.document);
		}),
		workspace.onDidOpenTextDocument((document) => {
			if (document.uri.scheme !== DIAGNOSTICS_VIEW_SCHEME) return;
			decorateVisibleEditors(document);
		}),
		window.onDidChangeActiveTextEditor(async (editor) => {
			if (editor) await decorateVisibleEditors(editor.document);
		}),
		window.onDidChangeVisibleTextEditors(async (editors) => {
			for (const editor of editors) {
				await decorationProvider.provideDecorations(editor);
			}
		}),
	);
}

export function deactivate() {
	fileWatcher?.dispose();
	if (!client) return;
	return client.stop();
}
