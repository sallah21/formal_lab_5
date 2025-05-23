# ASIC Design & Validation academic example

This repository contains exemplary hardware design, written in SystemVerilog HDL, along with
flows for building/synthesizing/validating it. The purpose is to give students an idea on how the
digital hardware development workflow looks like.

## 1. Contents

This example includes the following parts:

- RTL design
- Formal property verification
- Datapath validation
- Superlint (hardware lint)
- High-level C++ model
- Design synthesis
- UVM enviromnent

## 2. Suggested workflow

It is highly recommended to use [Visual Studio Code](https://code.visualstudio.com/) as code editor,
because of its rich features, one of which is [DVT VS Code plugin](https://dvteclipse.com/products/dvt-ide-for-visual-studio-code).
This plugin makes VS Code a better hardware development environment than some of the other commercially available IDEs.
VS Code can also be entirely tailored to the end user - You can say that You create Your own IDE.

## 3. Prerequisites

Use the **setenv.sh** script to set up the required environment variables.

## 4. Disclaimers

The example does not provide any tool executables or exact instructions on how to use them.
It is assumed that all the required tools are pre-installed, as well as all the necessary licensing is provided.