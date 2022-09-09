# Changelog

#### v3.0.2

- Enhancement: add optimisation to generic fusion to prevent generating some
  small functions with many arguments that may cause fusion to stop because of
  the 32 arguments limit. Instead generate larger functions with fewer
  arguments by inlining function calls.
- Enhancement: speed up and reduce memory usage of compilation with generic
  fusion. Instead of generating a new trivial function and inlining the
  function later do this immediately (without generating a new function) in
  some cases.
- Fix: the Windows version of `lib-compiler` now distributes `backend.dll` in
  `misc/dll/backend.dll` instead of `exe/backend.dll` to avoid a name clash
  with `base-compiler`.

#### v3.0.1

- Fix: prevent compiler crash when explicitly importing a macro using a new
  type pattern match.

## v3.0

- Feature: add `{ :}`, `{! :}`, `{# :}`, and `{32# :}` array types which
  reserve up to the next power of 2 of memory. This uses the ABC instructions
  `create_arrayp2` and `create_arrayp2_`.
- Feature: add functional dependencies (backported from the iTasks compiler).
- Feature: add `import qualified .. as ..` (backported from the iTasks
  compiler).
- Feature: add `binumap` (backported from the iTasks compiler).
- Fix: fix printing of higher-order array types.
- Fix: prevent stack overflow when compiling very large function types.

#### v2.0.1

- Chore: allow `base-stdenv` ^2.0.

## v2.0

- Enhancement: use ABC instructions `select_nc` and `update_nc` for array
  updates and selects when indexes do not need to be checked (e.g. in array
  comprehensions).
- Enhancement: add names of comprehensions to generated identifiers in
  patterns.
- Fix: bug in generic fusion causing incorrect functions to be generated.

## v1.0

First tagged version.
