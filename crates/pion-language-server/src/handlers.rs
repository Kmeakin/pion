use lsp_server::{Notification, Request, Response};
use lsp_types::notification::{DidChangeTextDocument, DidOpenTextDocument, Notification as _};
use lsp_types::{DidChangeTextDocumentParams, DidOpenTextDocumentParams};
use pion_utils::source::SourceFile;

use crate::{convert, diagnostics, Server};

mod document_symbols;

pub fn handle_request(server: &Server, request: Request) -> anyhow::Result<()> {
    use lsp_types::request::{DocumentSymbolRequest, Request};

    match request.method.as_str() {
        DocumentSymbolRequest::METHOD => document_symbols::handle(server, request)?,
        _ => eprintln!("TODO: handle request {request:?}"),
    }

    Ok(())
}

#[allow(clippy::unnecessary_wraps)]
#[allow(unused_variables)]
#[allow(clippy::needless_pass_by_value)]
pub fn handle_response(server: &Server, response: Response) -> anyhow::Result<()> {
    eprintln!("TODO: handle response {response:?}");
    Ok(())
}

pub fn handle_notification(server: &mut Server, notification: Notification) -> anyhow::Result<()> {
    match notification.method.as_str() {
        DidOpenTextDocument::METHOD => handle_open_text_document(server, notification),
        DidChangeTextDocument::METHOD => handle_did_change_text_document(server, notification),
        _ => {
            eprintln!("TODO: handle notification {notification:?}");
            Ok(())
        }
    }
}

fn handle_open_text_document(
    server: &mut Server,
    notification: Notification,
) -> anyhow::Result<()> {
    let params = serde_json::from_value::<DidOpenTextDocumentParams>(notification.params)?;
    let url = params.text_document.uri;
    let path = convert::url_to_path(&url)?;
    let file = SourceFile::read(path)?;
    server.insert_file(file);
    diagnostics::report_diagnostics(server)?;
    Ok(())
}

fn handle_did_change_text_document(
    server: &mut Server,
    notification: Notification,
) -> anyhow::Result<()> {
    let params = serde_json::from_value::<DidChangeTextDocumentParams>(notification.params)?;
    let url = params.text_document.uri;
    let path = convert::url_to_path(&url)?;
    let file = SourceFile::read(path)?;
    server.insert_file(file);
    diagnostics::report_diagnostics(server)?;
    Ok(())
}
