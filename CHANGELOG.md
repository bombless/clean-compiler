# Changelog

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
