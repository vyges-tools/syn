# vyges-syn

Integrated logic synthesis from RTL to a mapped netlist, on the shared AIG core.

> **Status: in development.** Every command currently refuses with exit 3. Commands are enabled one
> at a time as each is validated.

## Why this exists

Synthesis inside the suite, on the same AIG core as restructuring and formal, so a flow can run from RTL to layout without leaving it.

## Usage

```
vyges physical syn run <job>
vyges physical syn --describe
```

## Install

```
vyges install physical
```

## License

Apache-2.0. See `LICENSE` and `NOTICE`.
