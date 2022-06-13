# compiler

This is the repository of the [Clean][] compiler.

This is a delayed mirror of the [upstream][] version and is only used to
publish the package. Periodically changes from upstream are released in a new
version here.

The compiler is released in the `base-compiler` and `base-compiler-itasks`
packages. A library with compiler sources is distributed as
`lib-compiler-itasks`. `base-compiler` should normally not be used directly;
instead, you should use `base`.

See the documentation in [base][] if you intend to make a merge request for
this repository.

## Packages

In this repository the sources of three packages are kept:

- [`base-compiler`][base-compiler] (from the [`main`][main] branch), which is
  the standard compiler. This package should not be included directly, but
  through [`base`][base].

- [`base-compiler-itasks`][base-compiler-itasks] (from the [`itasks`][itasks]
  branch). This compiler is not included in [`base`][base].

- [`lib-compiler-itasks`][lib-compiler-itasks] (from the [`itasks`][itasks]
  branch). This is a library with which you can use modules from the Clean
  compiler.

The versions of these packages are kept in sync. This means:

- `base-compiler-itasks` may introduce features in patch versions.
- `lib-compiler-itasks` patch versions may not be backwards compatible.
  Normally you will want to use this dependency with an exact version
  constraint, e.g. `=1.0.0`.

## Maintainer & license

This project is maintained by [Camil Staps][].
The upstream is maintained by John van Groningen.

For license details, see the [LICENSE](/LICENSE) file.

[base]: https://clean-lang.org/pkg/base/
[base-compiler]: https://clean-lang.org/pkg/base-compiler/
[base-compiler-itasks]: https://clean-lang.org/pkg/base-compiler-itasks/
[Camil Staps]: https://camilstaps.nl
[Clean]: https://clean-lang.org/
[itasks]: https://gitlab.com/clean-and-itasks/base/compiler/-/tree/itasks
[lib-compiler-itasks]: https://clean-lang.org/pkg/lib-compiler-itasks/
[main]: https://gitlab.com/clean-and-itasks/base/compiler/-/tree/main
[upstream]: https://gitlab.com/clean-compiler-and-rts/compiler
