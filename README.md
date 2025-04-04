# AI for Mathematics and Theoretical Computer Science: Lean Tutorial

We will use this repository for the Lean tutorial and exercises sessions of the [AI for Mathematics and Theoretical Computer Science](https://simons.berkeley.edu/workshops/simons-institute-theory-computing-slmath-joint-workshop-ai-mathematics-theoretical#simons-tabs) workshop.

The tutorial session given on April 7th, 11:30-12:30 will follow the `Tutorial.lean` file. For an expanded version of this tutorial, look at the `Introduction.lean` and `Shorter.lean` files. The latter contains some exercises.

If you have no previous Lean experience, we suggest that during the exercise sessions you work on the exercises in the files `Rewriting.lean`, `Iff.lean`, `Forall.lean` and `Exists.lean` in the `Exercises` folder. 

If you have some previous Lean experience, you might instead choose to work on one file from the
`Topics` folder. Of course, you can play with all files from that folder if you
have even more time.

A more comprehensive learning resource is the book [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).

You can either work with a local installation of Lean, or use an online version with no registration required.
Please see below for detailed instructions for each option.

## Local installation

If you want the full luxury Lean experience, you should install it on your
computer. After installing Lean, open a terminal and execute the commands listed below.

1. To install Lean, follow the instructions [here](https://leanprover-community.github.io/get_started.html).
2. Then download this repository using `git clone https://github.com/mariainesdff/ai_math_tcs.git`.
4. Run `cd ai_math_tcs`.
5. Run `lake exe cache get!` to download built dependencies.
6. Launch VS Code, either through your application menu or by typing `code .`. (MacOS users need to take a one-off extra step to be able to launch VS Code from the command line.)
7. If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder `ai_math_tcs` (**not** one of its subfolders).

## Online version, no registration

If you don’t want to install Lean, you can use the [lean4web server](https://live.lean-lang.org/) hosted by the [Lean FRO](https://lean-fro.org/).

An expanded version of the Lean tutorial given on April 7th is available accross the next two files: 

* first read [the introduction file](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FIntroduction.lean)
* then read and edit the [explanations and exercises file](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FShorter.lean)

The following files contain additional exercises that you can work on during the afternoon sessions:

* [rewriting](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F01Rewriting.lean)
* [iff](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F02Iff.lean)
* [forall](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F03Forall.lean)
* [exists](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F04Exists.lean)

You can refer to the [tactics cheatsheet](tactics.pdf) while doing the
exercises. Tactics are explained in the Lean file, but the pdf can be more
convenient as a reference.

## Authorship Note

This repository has been forked from the [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean/) repository by Patrick Massot. The differences are the addition of the `Tutorial.lean` file and its solutions, and of adapted instructions in this README.
