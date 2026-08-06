module

public meta import Lean.Parser.Term

@[expose] public section

/-! # Utility for syntax -/

/-! ## Aliases for syntax parsers -/

namespace Syntax

/-- Alias for `Lean.Parser.Term.funBinder` -/
@[run_parser_attribute_hooks]
meta abbrev funBinder := Lean.Parser.Term.funBinder

/-- Alias for `Lean.Parser.Term.matchAlts` -/
@[run_parser_attribute_hooks]
meta abbrev matchAlts := Lean.Parser.Term.matchAlts

end Syntax

/-! ## Delaboration rules -/

/-- `delab_rules f | pattern => rhs …` defines an `app_unexpander` for `f`
  by pattern matching, as a shorthand -/
syntax (name := delabRules) attrKind "delab_rules" ident Syntax.matchAlts : command
macro_rules
  | `($attr:attrKind delab_rules $f $[| $p => $s]*) => do
    `(@[$attr app_unexpander $f]
      meta def unexpander : Lean.PrettyPrinter.Unexpander
        $[| $p => $s]*
        | _ => throw ())
