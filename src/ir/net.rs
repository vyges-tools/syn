// SPDX-License-Identifier: Apache-2.0
//! Nets, three-valued constants and control nets.
//!
//! A net is a slot in the graph's table: ids 0, 1 and 2 are the constants (zero, one, undefined),
//! every other id is one output bit of an instance. `u32::MAX` is a sentinel ("no net").

use std::fmt;

/// One output bit: the id of its table slot.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Net(pub u32);

impl Net {
    pub const ZERO: Net = Net(0);
    pub const ONE: Net = Net(1);
    pub const UNDEF: Net = Net(2);
    pub const SENTINEL: Net = Net(u32::MAX);

    pub fn id(self) -> u32 {
        self.0
    }
    pub fn is_const(self) -> bool {
        self.0 <= 2
    }
    pub fn is_sentinel(self) -> bool {
        self.0 == u32::MAX
    }
    pub fn const_trit(self) -> Trit {
        match self.0 {
            0 => Trit::Zero,
            1 => Trit::One,
            _ => Trit::Undef,
        }
    }
    pub fn from_trit(t: Trit) -> Net {
        match t {
            Trit::Zero => Net::ZERO,
            Trit::One => Net::ONE,
            Trit::Undef => Net::UNDEF,
        }
    }
}

/// A bundle of nets, least significant first.
pub type Bundle = Vec<Net>;

/// `width` consecutive nets from `base`.
pub fn consecutive(base: Net, width: u32) -> Bundle {
    (0..width).map(|i| Net(base.0 + i)).collect()
}

/// Every net a constant (an empty bundle counts).
pub fn is_const(b: &[Net]) -> bool {
    b.iter().all(|n| n.is_const())
}

/// Three-valued logic.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Trit {
    Zero = 0,
    One = 1,
    Undef = 2,
}

impl fmt::Display for Trit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Trit::Zero => "0",
            Trit::One => "1",
            Trit::Undef => "X",
        })
    }
}

/// A multi-bit constant, least significant first.
pub type Const = Vec<Trit>;

/// A net with a polarity: active high (positive) or active low.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ControlNet {
    pub net: Net,
    pub positive: bool,
}

impl Default for ControlNet {
    fn default() -> Self {
        ControlNet::ZERO
    }
}

impl ControlNet {
    pub const ZERO: ControlNet = ControlNet { net: Net::ZERO, positive: true };
    pub const ONE: ControlNet = ControlNet { net: Net::ONE, positive: true };

    pub fn pos(net: Net) -> Self {
        ControlNet { net, positive: true }
    }
    pub fn neg(net: Net) -> Self {
        ControlNet { net, positive: false }
    }
    pub fn with_polarity(net: Net, positive: bool) -> Self {
        ControlNet { net, positive }
    }
    /// The control is constantly active (`active`) or constantly inactive.
    pub fn is_always(self, active: bool) -> bool {
        let level = if self.positive { active } else { !active };
        self.net == if level { Net::ONE } else { Net::ZERO }
    }
}
