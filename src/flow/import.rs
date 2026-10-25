// SPDX-License-Identifier: Apache-2.0
//! Library cells the design instantiates (opaque `other` cells named after a Liberty cell) become
//! target cells.

use crate::ir::Graph;

/// Normalizes, then turns every `other` cell that names a loaded library cell into a target.
/// ⚠️ No library can be loaded yet: no cell matches, so only the normalize happens.
pub fn import_targets(g: &mut Graph) {
    g.normalize();
}
