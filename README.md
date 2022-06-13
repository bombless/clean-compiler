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

To update the `itasks` branch, first merge the upstream `itask` and then merge
the version and changelog changes:

```bash
git checkout itasks
git merge upstream/itask
git merge main
```

After each merge you may have to resolve conflicts (and finish the merge with
`git commit`). You may also have to add extra changelog entries if the `itask`
branch includes more changes.

Push all branches:

```bash
git push origin refs/remotes/upstream/itask:refs/heads/upstream-itask
git push origin refs/remotes/upstream/master:refs/heads/upstream-master
git push origin main:main
git push origin itasks:itasks
```

Head over to https://gitlab.com/clean-and-itasks/base/compiler/-/network/main
to check that all looks good. No commit should be listed twice.

If all looks good and pipelines succeed, you can tag the new heads and push the
tags:

```bash
git tag -s VERSION -m VERSION main
git push origin VERSION
git tag -s VERSION-itasks -m VERSION-itasks main
git push origin VERSION-itasks
```

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
