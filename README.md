#TL System Fork
This is a fork of Dr. Victor Winter's TL System (http://faculty.ist.unomaha.edu/winter/ShiftLab/TL_web/TL_index.html)

The interim goal of this fork to align the TL System build structure with that of LLVM. 

The end state goal is complete LLVM integration including:

1. LLVM pass, analysis, and rewrite
2. Build chain integration including ARM targets.



TL_System
=========

The TL System is a collection of functions providing general-purpose support for rewrite-based transformation over elements 
belonging to a (user-defined) domain language. 

In the TL System, a domain language is described by a tuple consisting of:

1. an EBNF grammar and
2. a lexical specification of tokens.

The command-line architecture of the TL system has been designed to support the use of TL System functions 
in specific ways. 

The command-line architecture consists of three folders:

1. a folder called Bat Commands containing (DOS) dot-bat files can be used at the system-level to create artifacts central to rewrite-based transformation (e.g, a domain-language parser, a pretty-printed version of a target program, etc.),
2. a folder containing domain-specific data, and 
3. a folder called TL_System.

The command-line architecture of the TL System has been designed to provide functionality suitable to both domain developers as well as domain clients. By domain developer we mean a person whose activities include:

- Specification of the domain language syntax.
 - Development of transformations appropriate to a domain. This includes:
  - Implementation of transformations expressed in the language TL.
  - Implementation of general-purpose functionality expressed in the language SML.
- Development of style rules for pretty-printing parse trees belonging to a domain.

In contrast, a domain client is a person whose activities include:

- Writing programs in the domain language, and applying transformations to these programs.
