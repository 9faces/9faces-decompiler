# 9faces Decompiler

A headless executor-side Luau bytecode reader, disassembler, and source reconstructor. It does not create a separate window and does not call an external decompiler API.

## Current native reconstruction

- Reads Luau bytecode versions 3 through 14.
- Reconstructs common forward branches, if/else blocks, while loops, repeat loops, numeric for loops, and generic for loops.
- Reconstructs nested closures and captured upvalues.
- Handles fixed and recoverable variable-argument calls and returns.
- Rebuilds common table constructors and constant-backed table templates.
- Tracks register values and scopes across reconstructed blocks.
- Folds safe constant arithmetic and selected deterministic string, math, and bit32 calls.
- Supports PascalCase output names by default.

## Executor integration

Load `Loader.lua` in the executor environment. The loader exposes `Ninefaces.Decompile`, `Ninefaces.Disassemble`, `Ninefaces.Parse`, `Ninefaces.Inspect`, `Ninefaces.GetStatus`, and `Ninefaces.SetBytefallFallback`.

Valm Dex ++ loads this file as its primary decompiler. Its existing Bytefall implementation remains the first fallback when a bytecode pattern cannot be reconstructed.

## Limits

The native reconstructor is heuristic rather than a complete Luau compiler decompiler. Heavy control-flow flattening, virtualized state machines, irreducible branch graphs, unsupported class opcodes, and some executor-specific bytecode extensions may still require a fallback. It only receives bytecode the executor exposes for the selected script.
