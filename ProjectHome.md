Implementing a compiler for the CL language.

The CL language
Essentially, CL contains INT and BOOL as basic types (with the usual meaning), and type
constructors ARRAY [hsizei](hsizei.md) OF htypei, and STRUCT hfield listi ENDSTRUCT with the
usual meaning.
Expressions are constructed in the classical way, with the standard binary operators
\+, -, 