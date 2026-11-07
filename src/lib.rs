//! Native expression analysis for embedding in an agent loop.
//! Call [`engine::initialize`] at startup, then [`engine::evaluate`] for each expression.
mod affine;
pub mod engine;
pub mod frontend;
