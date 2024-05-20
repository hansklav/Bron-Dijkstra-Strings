MODULE BronDijkstraStrings;  (* hk  2 Feb 2024 *)
(* 
  C. Bron & E.J. Dijkstra,  
  A Better Way to Combine Efficient String Length Encoding and Zero-termination.
  SIGPLAN Notices 1988, Vol. 24, No. 6, p. 11-19.
  
  In the following lwb(s) and upb(s) stand for the lower and upper bound 
  of the index range of the character array containing the string.
  
  In Oberon:  lwb(s) = 0;             (* lower bound of string container *)
              upb(s) = LEN(str) - 1;  (* upper bound of string container *) 
  
  The last element of s is s[upb(s)].
  This value will primarily be interpreted as the distance from the end of s where 
  the null-terminator may be found if the string s contains a null-terminator at all.
  Note: in Oberon the null-terminator 0X is obligatory.
  
  This encoding has a number of attractive properties:
  - if the last character in the string container is a null-character, 
    it indeed locates the position of the (terminating) null-character.
  - if the position in the string so designated does not contain a null-character, 
    the string is 'full', i.e. the number of relevant characters in the string equals 
    the size of the string container, and it is, consequently, not null-terminated
    (not applicable in Oberon-07).
  - if string containers are long (longer than, say, 256 bytes) and almost full, 
    only a small (byte-sized) integer will do to encode the end-of-string position. 
    If the long string container is far from full, the tail of the string container 
    has plenty of unused space to encode by means of some 'escape value' the position 
    of the terminating null-character as a more than byte-sized integer.
*)

  IMPORT Out;

  CONST 
    escVal = 0FFX;   (* escape value: 255 *)
    maxLen = 65791;  (* maximum BDstring length: 256*256+255 for 2-byte length encoding *)
    shortLen = 255; 
    longLen = 32768; (* 2^15, maximum length of string literals is 16381; VARs may be longer *)
    
  TYPE
    STRING* = ARRAY shortLen OF CHAR;
    LSTRING* = ARRAY longLen OF CHAR;
    Ccond* = PROCEDURE (c: CHAR): BOOLEAN;
    Pcond* = PROCEDURE (p: INTEGER): BOOLEAN;
    
    
  PROCEDURE MIN(i, j: INTEGER): INTEGER;
  BEGIN 
    IF i > j THEN i := j END
  RETURN i
  END MIN;
  

  PROCEDURE Length* (VAR s: ARRAY OF CHAR): INTEGER;                (* Originally: eos *)
  (* For Oberon-07, where it is guaranteed that: 
     - all strings are zero-terminated
     - all arrays are indexed starting from 0 (so lwb = 0)
     - strings never contain escVal (0FFX) as a character value 
  *)
    VAR upb, pos, res: INTEGER;
  BEGIN
    upb := LEN(s) - 1;         (* upper bound (highest index) of array s *)
    pos := upb - ORD(s[upb]);
    IF pos >= 0 THEN           (* ORD(s[upb]) is a valid index *)
      IF s[pos] = 0X THEN
        res := pos
      ELSIF s[upb] = escVal THEN
        (* now the encoding is relative to location 0 *)
        res := ORD(s[upb - 2]) * 256 + ORD(s[upb - 1]);
      ELSE
        Out.String("STRINGS.Length: encoding error 2"); Out.Ln;
        ASSERT(FALSE)     
      END
    ELSE
      Out.String("STRINGS.Length: encoding error 1"); Out.Ln;
      ASSERT(FALSE)
    END
  RETURN res
  END Length;
(*
  PROCEDURE Length* (s: ARRAY OF CHAR): INTEGER;                (* Originally: eos *)
  (* For implementations where it is not guaranteed that: 
     - all strings are zero-terminated
     - strings don't contain escVal (0FFX) as a character value 
  *)
    VAR upb, pos, res: INTEGER;
  BEGIN
    upb := LEN(s) - 1;         (* upper bound (highest index) of array s *)
    pos := upb - ORD(s[upb]);
    res := upb + 1;            (* default for non null-terminated *)
    IF pos >= 0 THEN           (* ORD(s[upb]) is a valid index *)
      IF s[pos] = 0X THEN
        res := pos
      ELSIF s[upb] = escVal THEN
        pos := ORD(s[upb - 2]) * 256 + ORD(s[upb - 1]);
        (* now the encoding is relative to location 0 *)
        IF (pos >= 0) & (pos <= upb) & (s[pos] = 0X) THEN
          res := pos
        END
      ELSE
        Out.String("String encoding error 2"); Out.Ln;
        ASSERT(FALSE)       
      END
    ELSE
      Out.String("String encoding error 1"); Out.Ln;
      ASSERT(FALSE)
    END
  RETURN res
  END Length;
*)
 
  PROCEDURE SetLength (VAR s: ARRAY OF CHAR; e: INTEGER);     (* Originally: terminate *)
  (*
    If an 'escape value' and two bytes must be used to encode the string length,
    then SetLength must ensure that:
       s[upb - ORD(escVal)] ≠ 0X 
    otherwise that position would erroneously be encoded as the end-of-string.
    That position will always be > 255 places from the upper array bound. 
  *)
    VAR upb, dist, escPos: INTEGER; 
  BEGIN upb := LEN(s) - 1;           (* upper bound (highest index) of array s *)
    IF e > maxLen - 1 THEN e := maxLen - 1
    ELSIF e > upb THEN e := upb
    END;
    dist := upb - e;                 (* distance from upb to 0X *)
    IF dist <= 255 THEN
      s[upb] := CHR(dist)            (* one-byte encoding *)
    ELSE
      escPos := upb - ORD(escVal);
      IF s[escPos] = 0X THEN s[escPos] := 1X END;  (* or some other non-0X value *)
      s[upb] := escVal;  
      s[upb - 1] := CHR(e MOD 256);  (* two-byte encoding for index of 0X:  *)
      s[upb - 2] := CHR(e DIV 256);  (* ORD(s[upb-2]) * 256 + ORD(s[upb-1]) *)
    END
  END SetLength;
  

  PROCEDURE Init* (VAR s: ARRAY OF CHAR);
  (* Makes s an empty string *)
  BEGIN
    s[0] := 0X;
    SetLength(s, 0)
  END Init;


  PROCEDURE IsEmpty* (VAR s: ARRAY OF CHAR): BOOLEAN;
  RETURN s[0] = 0X  (* also works after s := "" *)
  END IsEmpty;


  PROCEDURE Accept* (VAR s: ARRAY OF CHAR);
  (*
    Adapts a string (null-terminated or not) to the Bron-Dijkstra length convention.
    Finds the null-character or the end-of-string by a left-to-right scan and encodes 
    its length.
  *)
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE (s[i] # 0X) & (i < LEN(s) - 1) DO INC(i) END;
    SetLength(s, i)
  END Accept;


  PROCEDURE Copy0* (src: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR); (* Originally: assign *)
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE (src[i] # 0X) & (i < LEN(dest) - 1) DO
      dest[i] := src[i];
      INC(i)
    END;
    dest[i] := 0X;
    SetLength(dest, i)
  END Copy0;

  PROCEDURE Copy* (src: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR);
  (** Copy(src, dest) assigns src to dest without the strict type check of dest := src.
    It has the same effect as Delete(dest, 0, Length(dest)) followed by Insert(src, 0, dest)
    or as  dest := "";  Insert(src, 0, dest).
    This version is about 50% faster than Copy0.
  *)
    VAR i, n: INTEGER;
  BEGIN
    (* Init(dest); *) (* necessary if src = "" *)
    n := MIN(Length(src), LEN(dest) - 1);  
    FOR i := 0 TO n - 1 DO  (* copy n chars *)
      dest[i] := src[i] 
    END;
    dest[i] := 0X;
    Out.String("Copy: i = "); Out.Int(i, 0); Out.Ln;
    SetLength(dest, i)
  END Copy;


  PROCEDURE Append0* (extra: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR);
    VAR i, j, upb: INTEGER;
  BEGIN upb := LEN(dest) - 1;
    i := Length(dest);
    j := 0;
    WHILE (extra[j] # 0X) & (i < upb) DO
      dest[i] := extra[j];
      INC(i); INC(j)
    END;
    dest[i] := 0X;
    SetLength(dest, i)
  END Append0;
  
  PROCEDURE Append* (extra: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR);
  (** Append(s, dest) has the same effect as Insert(s, Length(dest), dest).
  *)
    VAR i, d0, d1: INTEGER;
  BEGIN
    d0 := Length(dest);  (* original length of dest *)
    d1 := MIN(d0 + Length(extra), LEN(dest) - 1);  (* new length of dest *)
    FOR i := d0 TO d1 - 1 DO dest[i] := extra[i - d0] END;
    dest[d1] := 0X;
    SetLength(dest, d1)
  END Append;


  PROCEDURE AppendChar0* (ch: CHAR; VAR dest: ARRAY OF CHAR);
    VAR s: ARRAY 2 OF CHAR;
  BEGIN 
    s[0] := ch;  s[1] := 0X;
    Append(s, dest)
  END AppendChar0;

  PROCEDURE AppendChar* (ch: CHAR; VAR dest: ARRAY OF CHAR);
  (* Is about 3x faster than AppendChar0 both for long and short strings *)
    VAR upb, len: INTEGER;
  BEGIN 
    upb := LEN(dest) - 1;
    len := Length(dest);
    IF len < upb THEN
      dest[len] := ch;
      dest[len + 1] := 0X;
      IF upb - len <= 255 THEN     (* one-byte length encoding *)
        IF len < upb - 1 THEN
          dest[upb] := CHR(ORD(dest[upb]) - 1)  (* DEC(dest[upb]) *)
        END
      ELSE                         (* two-byte length encoding *)
        SetLength(dest, len + 1)
      END
    END
  END AppendChar;


  PROCEDURE NextChar* (s: ARRAY OF CHAR; VAR pos: INTEGER): CHAR;
  (** NextChar() returns the next character in string s, starting from position pos.
    Parameter pos must be initialized to the position of the first character of s 
    to be delivered, and is updated to the next. 
    Calling this function for every single character to be retrieved is not the utmost 
    of efficiency, but its elegance lies in its delivering a null-character after the 
    last significant character, regardless of whether the null-character is actually 
    encoded in the string.
  *)
    VAR res: CHAR; 
  BEGIN
    IF pos > Length(s) - 1 THEN 
      res := 0X
    ELSE 
      res := s[pos]; INC(pos)
    END
  RETURN res
  END NextChar;


  PROCEDURE AppendUpto* ( extra: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR; 
                          VAR pos: INTEGER; c: CHAR );
  (** This procedure appends the part of extra onto dest, starting at extra[pos] upto
    (but not including) the first occurrence of the character c in extra, or (if c 
    is not found) upto the end of extra. 
    Upon completion pos satisfies: (pos = Length(extra)) OR (extra[pos] = c)
  *)
    VAR n, upb: INTEGER;
      ch: CHAR;
  BEGIN 
    upb := LEN(dest) - 1;        (* upper bound (highest index) of array dest *)
    n := Length(dest);           (* original number of characters in dest *)
    ch := NextChar(extra, pos);  (* each call increases pos by 1 *)
    WHILE ~(extra[pos] = c) & (ch # 0X) & (n < upb) DO 
      dest[n] := ch;
      INC(n);
      ch := NextChar(extra, pos)
    END;
    dest[n] := 0X;
    SetLength(dest, n)
  END AppendUpto;
  
  
  PROCEDURE AppendUptoCcond* ( extra: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR;
                               VAR pos: INTEGER; ccond: Ccond );
  (** This procedure appends the part of extra onto dest, starting at extra[pos] upto 
    (but not including) the first occurrence of ccond(extra[pos]) = TRUE, or 
    (if ccond(extra[pos]) is never TRUE), upto the end of extra.
    Upon completion pos satisfies:  (pos = Length(extra)) OR (ccond(extra[pos]))
  *)
    VAR n, upb: INTEGER;
      ch: CHAR;
  BEGIN 
    upb := LEN(dest) - 1;        (* upper bound (highest index) of array dest *)
    n := Length(dest);           (* original number of characters in dest *)
    ch := NextChar(extra, pos);  (* each call increases pos by 1 *)
    WHILE ~ccond(extra[pos]) & (ch # 0X) & (n < upb) DO 
      dest[n] := ch;
      INC(n);
      ch := NextChar(extra, pos)
    END;
    dest[n] := 0X;
    SetLength(dest, n)
  END AppendUptoCcond;
  

  PROCEDURE AppendUptoPcond* ( extra: ARRAY OF CHAR; VAR dest: ARRAY OF CHAR;
                               VAR pos: INTEGER; pcond: Pcond );
  (** This procedure appends that part of extra onto dest that start at extra[pos] upto 
    (but not including) the first occurrence of pcond(pos) = TRUE, or (if pcond(pos) is
    never TRUE) upto the end of extra. 
    Upon completion pos satisfies:  (pos = Length(extra)) OR (pcond(pos))
  *)
    VAR n, upb: INTEGER;
      ch: CHAR;
  BEGIN 
    upb := LEN(dest) - 1;        (* upper bound (highest index) of array dest *)
    n := Length(dest);           (* original number of characters in dest *)
    ch := NextChar(extra, pos);  (* each call increases pos by 1 *)
    WHILE ~pcond(pos) & (ch # 0X) & (n < upb) DO
      dest[n] := ch;
      INC(n);
      ch := NextChar(extra, pos)
    END;
    dest[n] := 0X;
    SetLength(dest, n)
  END AppendUptoPcond;


  PROCEDURE Compare(VAR s1, s2: ARRAY OF CHAR ): INTEGER; 
    VAR p1, p2: INTEGER; c1, c2: CHAR;
  BEGIN p1 := 0; p2 := 0;
    REPEAT c1 := NextChar( s1, p1 ); c2 := NextChar( s2, p2 ) 
    UNTIL (c1 # c2) OR (c1 = 0X);
  RETURN ORD(c1) - ORD(c2)
  END Compare;

  (* UNDER CONSTRUCTION *)

END BronDijkstraStrings.
