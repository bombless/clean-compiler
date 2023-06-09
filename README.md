# compiler

This is the repository of the [Clean][] compiler.

This is a delayed mirror of the [upstream][] version and is only used to
publish the package. Periodically changes from upstream are released in a new
version here.

See the documentation in [base][] and the notes on
[updating](/CONTRIBUTING.md#updating) if you intend to make a merge request for
this repository.

## Packages

In this repository the sources of three packages are kept:

- [`base-compiler`][base-compiler], which contains the compiler executable.
  This package should not be included directly, but through [`base`][base].

- [`lib-compiler`][lib-compiler]. This is a library with which you can use
  modules from the Clean compiler.

The versions of these packages are kept in sync. This means that `lib-compiler`
patch versions may not be backwards compatible. Normally you will want to use
this dependency with an exact version constraint, e.g. `=1.0.0`.

`base-compiler-itasks` and `lib-compiler-itasks` are old packages with a
special version of the compiler with extensions for iTasks. All extensions were
merged into `base-compiler` in June 2022.

See [CONTRIBUTING.md](CONTRIBUTING.md) for instructions on updating this
repository.

## Using the library

The Clean frontend of the compiler in `lib-compiler` can be used as any other
library.

On Windows systems, if an application uses not only the compiler frontend but
also the backend, it should copy `misc/dll/backend.dll` to the directory of the
executable.

On Unix systems, object code from the C backend is linked automatically if
needed.

## Maintainer & license

This project is maintained by [Camil Staps][].
The upstream is maintained by John van Groningen.

For license details, see the [LICENSE](/LICENSE) file.

[base]: https://clean-lang.org/pkg/base/
[base-compiler]: https://clean-lang.org/pkg/base-compiler/
[Camil Staps]: https://camilstaps.nl
[Clean]: https://clean-lang.org/
[itasks]: https://gitlab.com/clean-and-itasks/base/compiler/-/tree/itasks
[lib-compiler]: https://clean-lang.org/pkg/lib-compiler/
[main]: https://gitlab.com/clean-and-itasks/base/compiler/-/tree/main
[upstream]: https://gitlab.com/clean-compiler-and-rts/compiler
