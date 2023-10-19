# Deprecated lean4-samples repository.

This repository was prepared during the early development of Lean, and is now deprecated and unmaintained.

We do not recommend using it as a source for examples or teaching materials. Please see

* the Lean [language documentation](https://lean-lang.org/documentation/) and
* the Lean [community webpage](https://leanprover-community.github.io/)

for getting started.

## The future of this repo

If someone has a clear plan for this repository, and would like to take over maintainership and develop it into an up-to-date resource,
please contact us on [zulip](https://leanprover.zulipchat.com/).

----

# Old README contents
Code samples for Lean 4.  These samples are designed to work inside Visual Studio Code with the
Lean4 "extension".  The extension will install the Lean4 compiler and language service for you so it
is easy to setup - see the [Quick Start](https://leanprover.github.io/lean4/doc/quickstart.html) for
more information.

Currently each folder must be opened separately in Visual Studio Code for that sample to compile
correctly since each folder contains a separate Lean Package that is buildable using `lake build`.
Lake is the build system that comes with Lean.

## Get started

In order to run these samples you need a working Lean 4 environment.
See [Quickstart](https://leanprover.github.io/lean4/doc/quickstart.html)
instructions on how to set that up.

## Use Gitpod

You can also use [Gitpod](https://www.gitpod.io/docs/) to browse these samples and it will setup a
working Lean 4 environment for you.  Start by pointing your browser at
[https://gitpod.io/#https://github.com/leanprover/lean4-samples](https://gitpod.io/#https://github.com/leanprover/lean4-samples)
then when lean is installed use File/Open Folder... to open the sample that you want to play with.

See [Demo Video](https://youtu.be/_0QZXHoyZlA) showing how to do this.

## Use Github Codespaces

If you have a Github Team or Enterprise account you can also play with these samples in a [Github Codespace](https://docs.github.com/en/codespaces).

[![Open in GitHub Codespaces in West Europe](images/badge1.svg)](https://github.com/codespaces/new?hide_repo_select=true&ref=main&repo=452801263&machine=standardLinux32gb&location=WestEurope)

[![Open in GitHub Codespaces in West US](images/badge2.svg)](https://github.com/codespaces/new?hide_repo_select=true&ref=main&repo=452801263&machine=standardLinux32gb&location=WestUs2)

See [Demo Video](https://youtu.be/NLdM1_2TrfE) showing how it works.

## Hello world

Every language needs a [simple hello world sample](HelloWorld/README.md).

## Guess My Number

Explore more standard input processing with a [simple guess-my-number game](GuessMyNumber/README.md).

## CSV Parser

[CSV parser](CSVParser/README.md) is the simplest practical CSV parser you can write in Lean.

## Rubik's cube

[Rubik's cube](RubiksCube/README.md) is an example showing how to build custom [user widgets](https://leanprover.github.io/lean4/doc/examples/widgets.lean.html)
for the InfoView using TypeScript and Lake. Given a sequence of moves, it renders a Rubik's cube
in 3D which can be animated with the movement of a slider.


## List Comprehension using Syntax Extension

Explore how you can extend the Lean syntax to implement the popular python-style
[List Comprehension](ListComprehension/README.md).
