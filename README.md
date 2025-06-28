# Bron-Dijkstra-Strings

In [1988 C. Bron and E. J. Dijkstra](https://dl.acm.org/doi/10.1145/71052.71053) (click on download if github doesn't render the pdf) published an efficient way to combine string length encoding and zero-termination, well suited for languages such as Modula-2 and Oberon. Their proposal does not require any compiler or language change, provided the size of the string-container (character array) is known, either at run time or at compile time.

BronDijkstraStrings.Mod is an implementation for Oberon (all versions), Component Pascal or Modula-2.
TestBDstrings.Mod shows that this simple length encoding can accomplish a 50% to 300% efficiency gain in Copy and Append procedures.
