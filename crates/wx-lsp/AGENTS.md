# Language server guidance

Use the compiler's semantic data and shared queries for language behavior.
Preserve useful diagnostics and navigation on incomplete or erroneous source.

CLI and LSP formatting must agree byte for byte. Use `wx-fmt` and
`RendererConfig::from_manifest`; an already formatted document must return no
edits.

Keep file-watching registration in the server through
`client/registerCapability` for `*.wx` and `wx.json`. Editor integrations rely on
this to receive changes outside open buffers. Test document and manifest changes
through the existing server tests when changing refresh behavior.
