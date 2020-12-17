flatcurry-type-annotated
========================

This package contain libraries to represent FlatCurry programs with
type annotations. Thus, it is a specialization of the package
`flatcurry-annotated` which defines FlatCurry programs with
arbitrary annotations.

Furthermore, it contains libraries to annotate each expression
occurring in a given FlatCurry program with type information.
For this purpose, the library `FlatCurry.Annotated.TypeInference`
exports a main operation

    inferProg :: Prog -> IO (Either String (AProg TypeExpr))

which annotates a FlatCurry program with type information.

