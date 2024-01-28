#![allow(deprecated)]
// REASON: `deprecated` field is deprecated, but there is no other way to
// construct a `DocumentSymbol`

use lsp_server::{Message, Request, Response};
use lsp_types::{DocumentSymbol, SymbolKind};
use pion_surface::syntax::CstNode;
use pion_utils::source::SourceFile;

use crate::convert;
use crate::server::Server;

pub fn handle(server: &Server, request: Request) -> anyhow::Result<()> {
    use lsp_types::{DocumentSymbolParams, DocumentSymbolResponse};

    let params = serde_json::from_value::<DocumentSymbolParams>(request.params)?;
    let url = params.text_document.uri;
    let path = convert::url_to_path(&url)?;
    let file = SourceFile::read(path)?;

    let mut symbols = Vec::new();
    let (tree, _) = pion_surface::parse_source_file(&file.contents);
    let root: pion_surface::syntax::Root = CstNode::cast(tree.root()).unwrap();
    let source_file = root.source_file().unwrap();

    for item in source_file.items() {
        if let Some(symbol) = item_to_symbol(item, &file) {
            symbols.push(symbol);
        }
    }
    let response = DocumentSymbolResponse::Nested(symbols);

    server.send_message(Message::Response(Response {
        id: request.id,
        result: Some(serde_json::to_value(response)?),
        error: None,
    }))?;

    Ok(())
}

fn item_to_symbol(item: pion_surface::syntax::Item, file: &SourceFile) -> Option<DocumentSymbol> {
    match item {
        pion_surface::syntax::Item::NamespaceItem(namespace) => {
            let ident = namespace.ident_token()?;
            let name = ident.text();
            let item_range = convert::bytespan_to_lsp(namespace.syntax().span(), file).unwrap();
            let name_range = convert::bytespan_to_lsp(ident.span(), file).unwrap();

            Some(DocumentSymbol {
                name: name.to_owned(),
                detail: None,
                kind: SymbolKind::NAMESPACE,
                tags: None,
                deprecated: None,
                range: item_range,
                selection_range: name_range,
                children: Some(
                    namespace
                        .items()
                        .filter_map(|item| item_to_symbol(item, file))
                        .collect(),
                ),
            })
        }
        pion_surface::syntax::Item::DefItem(def) => {
            let ident = def.ident_token()?;
            let name = ident.text();
            let item_range = convert::bytespan_to_lsp(def.syntax().span(), file).unwrap();
            let name_range = convert::bytespan_to_lsp(ident.span(), file).unwrap();

            Some(DocumentSymbol {
                name: name.to_owned(),
                detail: None,
                kind: SymbolKind::CONSTANT,
                tags: None,
                deprecated: None,
                range: item_range,
                selection_range: name_range,
                children: None,
            })
        }
    }
}
