# vyges-syn

Integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.

> **Status: in development.** `synthesize` (SystemVerilog elaborated, synthesized onto the
> libraries' cells and written as a structural Verilog netlist), `sv-elaborate`, `ir-pass` and
> `ir-normalize` are built; `run` refuses with exit 3. Commands are enabled one at a time as each is
> validated.

## Why this exists

Synthesis inside the suite, on the same AIG core as restructuring and formal, so a flow can run from RTL to layout without leaving it.

## Usage

```
vyges physical syn synthesize --liberty LIB... --lef TECH.lef --lef CELLS.lef -o OUT.v \
    -- top.sv [--top NAME] [other slang arguments]
vyges physical syn sv-elaborate [--raw] [--liberty LIB]... -o OUT.ir <slang arguments...>
vyges physical syn ir-pass [--liberty LIB]... <in.ir> -o OUT.ir PASS...
vyges physical syn ir-normalize <in.ir> -o OUT.ir
vyges physical syn run <job>
vyges physical syn --describe
```

## Events

Every command leaves a causal trail of [`vyges-events`](https://github.com/vyges-tools/events) JSON
lines on **stderr**; netlists, reports and log lines go to stdout or `-o`, so either can be parsed without the other.

| code | meaning |
|---|---|
| `SYN-INPUT` | an input could not be read or an output written (exit 2) |
| `SYN-REFUSED` | the command, or what it was asked to do, is not implemented in this build (exit 3) |
| `SYN-STEP` | one step of the command, at `debug` |
| `SYN-DONE` | every command: its status (`ok`, `finding`, `input`, `refused`) and exit code |

`-q` / `--quiet`, given before the command (after it, `-v` belongs to the
SystemVerilog frontend), raises the trail's floor to `error`; `-v` / `--verbose` lowers it to `debug`.
An explicit `VYGES_LOG` in the environment wins over both.

## Install

```
vyges install physical
```

## License

Apache-2.0. See `LICENSE` and `NOTICE`.
