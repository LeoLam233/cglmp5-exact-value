import CGLMP5.CertificateSyntax

namespace CGLMP5.CertificateSource

/-- Source lines are kept separate so the kernel never constructs a megabyte UTF-8 buffer. -/
def prefixLine (p : String) : List String → List String
  | [] => [p]
  | h :: t => (p ++ h) :: t

def suffixLine (s : String) : List String → List String
  | [] => [s]
  | [h] => [h ++ s]
  | h :: t => h :: suffixLine s t

def arrayLines {α : Type} (render : Nat → α → List String) (n : Nat) (xs : List α) : List String :=
  if xs.isEmpty then ["[]"] else
    ["["] ++ (xs.zipIdx.map fun (x,j) =>
      prefixLine (spaces (n+2)) (suffixLine (if j+1<xs.length then "," else "")
        (render (n+2) x))).flatten ++ [spaces n ++ "]"]

def RawScalar.renderLines (n : Nat) (s : RawScalar) : List String :=
  ["{"] ++ prefixLine (spaces (n+2) ++ "\"n\": ")
    (suffixLine "," (arrayLines (fun _ v => [quote (toString v)]) (n+2) s.numerators)) ++
    [spaces (n+2) ++ "\"d\": " ++ quote (toString s.denominator), spaces n ++ "}"]

def factorLines (n : Nat) (a : Nat × Nat) : List String :=
  arrayLines (fun _ v => [toString v]) n [a.1,a.2]

def RawCoefficient.renderLines (n : Nat) (c : RawCoefficient) : List String :=
  ["{"] ++ prefixLine (spaces (n+2) ++ "\"word\": ")
    (suffixLine "," (arrayLines factorLines (n+2) c.word)) ++
    prefixLine (spaces (n+2) ++ "\"coefficient\": ") (c.coefficient.renderLines (n+2)) ++
    [spaces n ++ "}"]

def RawTerm.renderLines (n : Nat) (t : RawTerm) : List String :=
  ["{", spaces (n+2) ++ "\"id\": " ++ quote t.label ++ ","] ++
    prefixLine (spaces (n+2) ++ "\"weight\": ") (suffixLine "," (t.weight.renderLines (n+2))) ++
    prefixLine (spaces (n+2) ++ "\"polynomial\": ")
      (arrayLines RawCoefficient.renderLines (n+2) t.polynomial) ++ [spaces n ++ "}"]

def RawRational.renderLines (n : Nat) (q : RawRational) : List String :=
  ["{", spaces (n+2) ++ "\"numerator\": " ++ quote (toString q.numerator) ++ ",",
    spaces (n+2) ++ "\"denominator\": " ++ quote (toString q.denominator), spaces n ++ "}"]

def RawBox.renderLines (n : Nat) (b : RawBox) : List String :=
  ["{"] ++ prefixLine (spaces (n+2) ++ "\"lower\": ") (suffixLine "," (b.lower.renderLines (n+2))) ++
    prefixLine (spaces (n+2) ++ "\"upper\": ") (b.upper.renderLines (n+2)) ++ [spaces n ++ "}"]

def boxesLines (mu s u : RawBox) : List String :=
  ["{"] ++ prefixLine "    \"mu\": " (suffixLine "," (mu.renderLines 4)) ++
    prefixLine "    \"sqrt5\": " (suffixLine "," (s.renderLines 4)) ++
    prefixLine "    \"u\": " (u.renderLines 4) ++ ["  }"]

end CGLMP5.CertificateSource
