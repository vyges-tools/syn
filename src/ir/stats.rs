// SPDX-License-Identifier: Apache-2.0
//! The graph's cell counts: per kind (a library cell by its name, an opaque cell by its type),
//! cells, output bits and area, then the totals.

use std::collections::BTreeMap;
use std::fmt::Write;

use super::{Graph, Kind};

/// A number as a C++ stream prints a float by default: six significant digits, fixed notation
/// for exponents -4 to 5 and scientific (`1.5e+06`) otherwise, trailing zeros dropped.
pub fn fmt_g(x: f64) -> String {
    if x == 0.0 {
        return if x.is_sign_negative() { "-0".into() } else { "0".into() };
    }
    if !x.is_finite() {
        return if x.is_nan() { "nan".into() } else if x > 0.0 { "inf".into() } else { "-inf".into() };
    }
    let sci = format!("{x:.5e}");
    let (mantissa, exp) = sci.split_once('e').unwrap();
    let exp: i32 = exp.parse().unwrap();
    let trim = |s: &str| -> String {
        if s.contains('.') {
            s.trim_end_matches('0').trim_end_matches('.').to_string()
        } else {
            s.to_string()
        }
    };
    if !(-4..6).contains(&exp) {
        format!("{}e{}{:02}", trim(mantissa), if exp < 0 { '-' } else { '+' }, exp.abs())
    } else {
        trim(&format!("{:.*}", (5 - exp) as usize, x))
    }
}

impl Graph {
    /// Every instance but the ties, by kind in name order, then the totals; area where nonzero.
    pub fn stats(&self) -> String {
        #[derive(Default)]
        struct CellStats {
            cells: u32,
            bits: u32,
            area: f32,
        }
        let mut counts: BTreeMap<String, CellStats> = BTreeMap::new();
        let (mut total_cells, mut total_bits, mut total_area) = (0u32, 0u32, 0.0f32);
        for id in self.instance_list() {
            let kind = &self.inst(id).kind;
            if kind.is_tie() {
                continue;
            }
            let mut area = 0.0f32;
            let name = match kind {
                Kind::Other(o) => o.cell_type.clone(),
                Kind::Target(cell, _) => {
                    area = cell.area;
                    format!("target: {}", cell.name)
                }
                Kind::Name(n) if n.tentative => "name (tentative)".into(),
                k => k.keyword().into(),
            };
            let w = self.inst(id).output_width();
            let s = counts.entry(name).or_default();
            s.cells += 1;
            s.bits += w;
            s.area += area;
            total_cells += 1;
            total_bits += w;
            total_area += area;
        }
        let mut os = String::new();
        for (name, s) in &counts {
            let _ = write!(os, "  {name}: {} cells, {} bits", s.cells, s.bits);
            if s.area > 0.0 {
                let _ = write!(os, ", area {}", fmt_g(s.area as f64));
            }
            os.push('\n');
        }
        let _ = write!(os, "  total: {total_cells} cells, {total_bits} bits");
        if total_area > 0.0 {
            let _ = write!(os, ", area {}", fmt_g(total_area as f64));
        }
        os.push('\n');
        os
    }
}

#[cfg(test)]
mod tests {
    use super::fmt_g;

    // Rule: the default float format is %g with six significant digits.
    #[test]
    fn floats_print_as_six_significant_digits() {
        assert_eq!(fmt_g(5.32), "5.32");
        assert_eq!(fmt_g(1234567.0), "1.23457e+06");
        assert_eq!(fmt_g(123456.0), "123456");
        assert_eq!(fmt_g(0.0001), "0.0001");
        assert_eq!(fmt_g(0.00001234), "1.234e-05");
        assert_eq!(fmt_g(0.532f32 as f64), "0.532");
        assert_eq!(fmt_g(10.0), "10");
    }
}
