# Contributing

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

**Do not forget to update the version of the `lib-compiler` package as well!**

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
