use std::any::Any;

use cookie::CookieJar;
use hyper::upgrade::OnUpgrade;
use hyper::{HeaderMap, Method, Uri, Version};

use crate::helpers::http::request::path::RequestPathSegments;
use crate::state::request_id::RequestId;

#[cfg(feature = "derive")]
pub use gotham_derive::StateData;
use crate::core::body::Body;

/// A marker trait for types that can be stored in `State`.
///
/// This is typically implemented using `#[derive(StateData)]`.
///
/// ```rust
/// # use gotham::state::{FromState, State};
/// use gotham::state::StateData;
///
/// #[derive(StateData)]
/// struct MyStateData {
///     x: u32,
/// }
/// # fn main() {
/// #   State::with_new(|state| {
/// #       state.put(MyStateData { x: 1 });
/// #       assert_eq!(MyStateData::borrow_from(state).x, 1);
/// #   });
/// # }
/// ```


pub trait StateData: Any + Send {}

// TODO: Body 在 hyper 0.14 中 是 没有限定 !sync 的, 当前的实现是 允许他进行跨线程访问

impl StateData for Body {}
impl StateData for Method {}
impl StateData for Uri {}
impl StateData for Version {}
impl StateData for HeaderMap {}
impl StateData for CookieJar {}
impl StateData for OnUpgrade {}

impl StateData for RequestPathSegments {}
impl StateData for RequestId {}
