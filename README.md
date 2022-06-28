# compiler

This is the repository of the [Clean][] compiler.

This is a delayed mirror of the [upstream][] version and is only used to
publish the package. Periodically changes from upstream are released in a new
version here.

See the documentation in [base][] and the notes on [updating](#updating) below
if you intend to make a merge request for this repository.

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

## Updating

When pulling in new commits from upstream, follow the following steps:

Set up the repositories:

```bash
git clone git@gitlab.com:clean-and-itasks/base/compiler.git
cd compiler
git remote add upstream https://gitlab.science.ru.nl/clean-compiler-and-rts/compiler.git
```

Update the `main` branch by merging changes:

```bash
git fetch --no-tags upstream
git checkout main
git merge upstream/master
```

You may now have to resolve conflicts (and finish the merge with `git commit`).

Update the version in `nitrile.yml` and add changelog entries:

```bash
vim -p nitrile.yml CHANGELOG.md
git commit -am 'Bump version to VERSION; add changelog entries'
```

Push all branches:

```bash
git push origin refs/remotes/upstream/master:refs/heads/upstream-master
git push origin main:main
```

Head over to https://gitlab.com/clean-and-itasks/base/compiler/-/network/main
to check that all looks good. No commit should be listed twice.

If all looks good and pipelines succeed, you can tag the new heads and push the
tags:

```bash
git tag -s VERSION -m VERSION main
git push origin VERSION
```

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
