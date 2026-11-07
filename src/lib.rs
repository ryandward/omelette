//! Absence-laundering analysis for JavaScript and TypeScript expressions, for embedding in an
//! agent loop. Call [`engine::initialize`] at startup, then [`engine::evaluate`] per
//! expression. See docs/architecture.md for the pipeline.
mod affine;
pub mod core;
pub mod engine;
pub mod lower;
