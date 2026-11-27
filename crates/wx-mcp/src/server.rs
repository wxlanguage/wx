//! The MCP server: the tools and the core library resource, served with
//! `rmcp`. Each tool's arguments are a type, from which `rmcp` derives the
//! schema the client shows the model; its documentation is the schema's.
//!
//! A tool answers with text, or with the reason it could not answer as a
//! result marked as an error, so the model reads why.

use std::path::Path;

use rmcp::handler::server::router::tool::ToolRouter;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{
	Implementation, ListResourcesResult, PaginatedRequestParams,
	ReadResourceRequestParams, ReadResourceResponse, ReadResourceResult,
	Resource, ResourceContents, ServerCapabilities, ServerConfig,
};
use rmcp::service::RequestContext;
use rmcp::{
	ErrorData, RoleServer, ServerHandler, ServiceExt, tool, tool_handler,
	tool_router,
};
use wx_compiler::vfs::{AbsolutePath, CORE_FILES, CoreFileSource};

use crate::analysis::Analysis;
use crate::tools;

/// What the client tells the model about the server and its tools.
const INSTRUCTIONS: &str = "\
Inspect WX packages with the compiler's own analysis. Every tool reloads the \
package from disk, so it sees your latest edits.
- Run wx_check after editing WX code.
- Learn an API with wx_outline (`package: \"core\"` for the core library), \
then wx_describe for one item.
- Items are named by their paths as written in the root package's entry \
file: its own items unprefixed (`net::Client`), a dependency's through the \
package instance naming it (`package \"json\" as json;` gives `json::Value`), \
core's unprefixed, as the prelude makes them. Paths the tools print can be \
passed back to them.
- The core library's source is the resource wx://core/main.wx.";

/// Serves the tools over stdin and stdout until the client disconnects.
pub async fn serve_stdio() -> Result<(), Box<dyn std::error::Error>> {
	WxServer::new()
		.serve(rmcp::transport::stdio())
		.await?
		.waiting()
		.await?;
	Ok(())
}

#[derive(Clone)]
pub(crate) struct WxServer {
	tool_router: ToolRouter<Self>,
}

#[tool_router]
impl WxServer {
	pub(crate) fn new() -> Self {
		Self {
			tool_router: Self::tool_router(),
		}
	}

	/// Check a WX package: every parse, type and lint diagnostic, with the
	/// source it points at. Run it after editing.
	#[tool(name = "wx_check")]
	fn check(
		&self,
		Parameters(options): Parameters<tools::CheckOptions>,
	) -> Result<String, String> {
		Ok(tools::check(&load(&options.path)?, &options))
	}

	/// List a package's items with their signatures and first doc line,
	/// ordered by path: the way to learn an API. Defaults to the root
	/// package; `package` names `core` or a dependency's key, whose public
	/// API is listed. An item marked internal is not reachable from other
	/// packages.
	#[tool(name = "wx_outline")]
	fn outline(
		&self,
		Parameters(options): Parameters<tools::OutlineOptions>,
	) -> Result<String, String> {
		tools::outline(&load(&options.path)?, &options)
	}

	/// Describe one item by path: its signature, the trait or impl it
	/// belongs to, its documentation, where it is defined, its members
	/// (methods and trait impls, variants, a module's items), the traits it
	/// implements, and for a trait what implements it.
	#[tool(name = "wx_describe")]
	fn describe(
		&self,
		Parameters(options): Parameters<tools::DescribeOptions>,
	) -> Result<String, String> {
		tools::describe(&load(&options.path)?, &options)
	}

	/// Find items by name across the package, its dependencies and core,
	/// among those the package can name. Matches a case-insensitive part of
	/// the name, or of the path when no name matches.
	#[tool(name = "wx_search")]
	fn search(
		&self,
		Parameters(options): Parameters<tools::SearchOptions>,
	) -> Result<String, String> {
		Ok(tools::search(&load(&options.path)?, &options))
	}

	/// Explain one line of code: what each name on it resolves to, with its
	/// type or signature and the path of the item it names.
	#[tool(name = "wx_inspect")]
	fn inspect(
		&self,
		Parameters(options): Parameters<tools::InspectOptions>,
	) -> Result<String, String> {
		tools::inspect(&load(&options.file)?, &options)
	}

	/// Every place an item is used, grouped by file, with each line's
	/// source. A trait member's uses include calls on the types
	/// implementing it.
	#[tool(name = "wx_references")]
	fn references(
		&self,
		Parameters(options): Parameters<tools::ReferencesOptions>,
	) -> Result<String, String> {
		tools::references(&load(&options.path)?, &options)
	}

	/// Build the package and show the WebAssembly module it compiles to, as
	/// WAT. Only for a package without errors.
	#[tool(name = "wx_wasm")]
	fn wasm(
		&self,
		Parameters(options): Parameters<tools::WasmOptions>,
	) -> Result<String, String> {
		tools::wasm(load(&options.path)?, &options)
	}
}

/// The package governing `path`, checked from what is on disk now.
fn load(path: &str) -> Result<Analysis, String> {
	Analysis::load(Path::new(path))
}

#[tool_handler(router = self.tool_router)]
impl ServerHandler for WxServer {
	fn get_info(&self) -> ServerConfig {
		ServerConfig::new(
			ServerCapabilities::builder()
				.enable_tools()
				.enable_resources()
				.build(),
		)
		.with_server_info(Implementation::new("wx", env!("CARGO_PKG_VERSION")))
		.with_instructions(INSTRUCTIONS)
	}

	/// Each embedded core file, as `wx://core/<file>`.
	async fn list_resources(
		&self,
		_request: Option<PaginatedRequestParams>,
		_context: RequestContext<RoleServer>,
	) -> Result<ListResourcesResult, ErrorData> {
		let resources = CORE_FILES
			.iter()
			.map(|(name, _)| {
				Resource::new(format!("wx://core{name}"), format!("core{name}"))
					.with_description(
						"The WX core library: primitives, traits and instruction declarations.",
					)
					.with_mime_type("text/x-wx")
			})
			.collect();
		Ok(ListResourcesResult::with_all_items(resources))
	}

	async fn read_resource(
		&self,
		request: ReadResourceRequestParams,
		_context: RequestContext<RoleServer>,
	) -> Result<ReadResourceResponse, ErrorData> {
		let uri = request.uri;
		let source = uri
			.strip_prefix("wx://core")
			.filter(|path| path.starts_with('/'))
			.and_then(|path| CoreFileSource::source(&AbsolutePath::new(path)))
			.ok_or_else(|| {
				ErrorData::resource_not_found(
					format!("no resource `{uri}`"),
					None,
				)
			})?;
		let contents =
			ResourceContents::text(source, uri).with_mime_type("text/x-wx");
		Ok(ReadResourceResult::new(vec![contents]).into())
	}
}

#[cfg(test)]
mod tests {
	use serde_json::{Value, json};
	use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

	use super::*;
	use crate::analysis::tests::Fixture;

	/// The responses to `requests`, sent one per line after initializing,
	/// as the server writes them.
	async fn exchange(requests: &[Value]) -> Vec<Value> {
		let (client, server) = tokio::io::duplex(1 << 20);
		let (server_read, server_write) = tokio::io::split(server);
		let running = tokio::spawn(async move {
			let service = WxServer::new()
				.serve((server_read, server_write))
				.await
				.unwrap();
			let _ = service.waiting().await;
		});
		let (client_read, mut client_write) = tokio::io::split(client);
		let mut lines = BufReader::new(client_read).lines();
		let initialize = json!({ "jsonrpc": "2.0", "id": 0, "method": "initialize",
			"params": { "protocolVersion": "2025-06-18", "capabilities": {},
				"clientInfo": { "name": "test", "version": "0" } } });
		let initialized =
			json!({ "jsonrpc": "2.0", "method": "notifications/initialized" });
		for message in [&initialize, &initialized] {
			client_write
				.write_all(format!("{message}\n").as_bytes())
				.await
				.unwrap();
		}
		let reply: Value =
			serde_json::from_str(&lines.next_line().await.unwrap().unwrap())
				.unwrap();
		assert_eq!(reply["result"]["serverInfo"]["name"], "wx");
		let mut responses = Vec::new();
		for request in requests {
			client_write
				.write_all(format!("{request}\n").as_bytes())
				.await
				.unwrap();
			let line = lines.next_line().await.unwrap().unwrap();
			responses.push(serde_json::from_str(&line).unwrap());
		}
		running.abort();
		responses
	}

	#[tokio::test]
	async fn the_tools_are_listed_and_called() {
		let fixture = Fixture::new(&[("main.wx", "func main() {}\n")]);
		let responses = exchange(&[
			json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/list" }),
			json!({ "jsonrpc": "2.0", "id": 2, "method": "tools/call",
				"params": { "name": "wx_check",
					"arguments": { "path": fixture.dir.to_str().unwrap() } } }),
		])
		.await;
		let mut names: Vec<_> =
			(responses[0]["result"]["tools"].as_array().unwrap().iter())
				.map(|tool| tool["name"].as_str().unwrap())
				.collect();
		names.sort_unstable();
		assert_eq!(
			names,
			[
				"wx_check",
				"wx_describe",
				"wx_inspect",
				"wx_outline",
				"wx_references",
				"wx_search",
				"wx_wasm"
			]
		);
		assert_eq!(responses[1]["result"]["isError"], false);
		assert_eq!(
			responses[1]["result"]["content"][0]["text"],
			"No errors found."
		);
	}

	/// A `limit` the client leaves out takes a default, which the schema
	/// states so the model knows how much it gets.
	#[tokio::test]
	async fn each_limit_states_its_default_in_the_schema() {
		let responses = exchange(&[
			json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/list" }),
		])
		.await;
		let tools = responses[0]["result"]["tools"].as_array().unwrap();
		for (name, default) in [
			("wx_check", 30),
			("wx_outline", 300),
			("wx_search", 40),
			("wx_references", 200),
			("wx_wasm", 2000),
		] {
			let tool = tools.iter().find(|tool| tool["name"] == name).unwrap();
			let limit = &tool["inputSchema"]["properties"]["limit"];
			assert_eq!(limit["default"], default, "{name}: {limit}");
		}
	}

	#[tokio::test]
	async fn a_failing_tool_is_a_result_marked_as_an_error() {
		let responses = exchange(&[
			json!({ "jsonrpc": "2.0", "id": 1, "method": "tools/call",
			"params": { "name": "wx_check", "arguments": { "path": "/" } } }),
		])
		.await;
		assert_eq!(responses[0]["result"]["isError"], true);
		let text = responses[0]["result"]["content"][0]["text"]
			.as_str()
			.unwrap();
		assert!(text.contains("not inside a wx package"), "{text}");
	}

	#[tokio::test]
	async fn the_core_source_is_a_resource() {
		let responses = exchange(&[
			json!({ "jsonrpc": "2.0", "id": 1, "method": "resources/list" }),
			json!({ "jsonrpc": "2.0", "id": 2, "method": "resources/read",
				"params": { "uri": "wx://core/main.wx" } }),
		])
		.await;
		let uris: Vec<_> = (responses[0]["result"]["resources"]
			.as_array()
			.unwrap()
			.iter())
		.map(|resource| resource["uri"].as_str().unwrap())
		.collect();
		assert!(uris.contains(&"wx://core/main.wx"), "{uris:?}");
		let text = responses[1]["result"]["contents"][0]["text"]
			.as_str()
			.unwrap();
		assert!(text.contains("pub trait Memory"), "the core's source");
	}
}
