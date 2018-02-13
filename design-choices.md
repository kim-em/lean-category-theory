There seem to be two significant fundamental choices in the design of a category theory library for Lean. One is whether the type of objects of the category should be bundled as a field, or exposed as a parameter. The other is whether there should be two independent universe levels for objects and morphisms, or just one.

In my independent work on my category theory library, I took the first choice in each case (bundled objects, independent universes). When I made a tentative pull request of a small part of the library to `mathlib`, Mario suggested that in each case I made the wrong choice. Since then I've been seriously exploring both options, and this document is my summary of the pros and cons. I may have made some mistakes!

--- Bundled objects vs unbundled objects ---


