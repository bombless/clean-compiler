# Changelog

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
