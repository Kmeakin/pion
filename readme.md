## Features
* [x] dependent lambda calculus
    * [x] local variables
    * [x] integer and boolean literals
    * [x] `let` expressions
    * [x] `fun` expressions
    * [x] `forall` expressions
    * [x] function application expressions
    * [x] propositional equality
    * [ ] type universes

* [ ] unification
    * [x] inferring types of unnanotated patterns
    * [x] hole expressions
    * [x] implicit arguments
      * [x] specialization
      * [x] generalization
    * [ ] pruning

* [ ] recursion
    * [x] `fix`
    * [ ] `let rec`
        * [ ] single recursive value binding
        * [ ] mutually recursive value bindings
    * [ ] termination checking

* [ ] aggregate types
    * [ ] dependent pairs
    * [ ] record types
    * [ ] sum types
    * [ ] row types

* [ ] pattern matching
    * [x] `if` expressions
    * [x] single-layer pattern matching over integers and booleans
    * [x] multi-layer pattern matching compilation w/ coverage checking
    * [ ] equality witness patterns
    * [ ] or-patterns
    * [ ] and-patterns
    * [ ] pattern guards

* [ ] user interface
    * [ ] `pion check`
    * [ ] `pion repl`
    * [ ] `pion fmt`

* [ ] documentation
    * [ ] code comments
    * [ ] specification
        * [x] Surface language
            * [x] Lexical syntax
            * [x] Context-free syntax
        * [ ] Core language
            * [ ] Reduction rules
            * [ ] Typing rules
    * [ ] bibliography
