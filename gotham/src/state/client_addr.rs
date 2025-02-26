//! Defines storage for the remote address of the client

use crate::state::{FromState, State, StateData};
use std::net::SocketAddr;

struct ClientAddr {
    addr: SocketAddr,
}

impl StateData for ClientAddr {}

pub(crate) fn put_client_addr(state: &mut State, addr: SocketAddr) {
    state.put(ClientAddr { addr })
}

/// Returns the client `SocketAddr` as reported by hyper, if one was present. Certain connections
/// do not report a client address, in which case this will return `None`.
///
/// # Examples
///
/// ```rust
/// # extern crate gotham;
/// # extern crate hyper;
/// # extern crate mime;
/// #
/// # use hyper::{Body, Response, StatusCode};
/// # use gotham::helpers::http::response::create_response;
/// # use gotham::state::{State, client_addr};
/// # use gotham::test::TestServer;
/// # use gotham::core::body::Body;
/// #
/// fn my_handler(state: State) -> (State, Response<Body>) {
///     let addr = client_addr(&state).expect("no client address");
///
///     let body = format!("{}", addr);
///     let response = create_response(
///         &state,
///         StatusCode::OK,
///         mime::TEXT_PLAIN,
///         body,
///     );
///
///     (state, response)
/// }
/// #
/// # fn main() {
/// #   let test_server = TestServer::new(|| Ok(my_handler)).unwrap();
/// #   let response = test_server
/// #       .client()
/// #       .get("http://localhost/")
/// #       .perform()
/// #       .unwrap();
/// #
/// #   assert_eq!(response.status(), StatusCode::OK);
/// #
/// #   let buf = response.read_body().unwrap();
/// #   // at the moment, can't actually force the client address
/// #   assert!(buf.starts_with(b"127.0.0.1"));
/// # }
pub fn client_addr(state: &State) -> Option<SocketAddr> {
    // 获取提交IP todo:: 相同 IP 如何判断不同的请求内容
    ClientAddr::try_borrow_from(state).map(|c| c.addr)
}
