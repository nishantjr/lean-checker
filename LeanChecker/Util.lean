--- TODO: We should use the standard library verion of this.
def getElement {α: Type} (n: Nat) (l: List α) : Option α :=
    match l with
    | [] => none
    | head :: tail
      => match n with
         | 0 => some head
         | n'+1 => getElement n' tail

--- TODO: We should use the standard library verion of this.
def append{α: Type} (l: List α) (e: α) : List α :=
    match l with
    | [] => e :: []
    | head :: tail => head :: (append tail e)

--- TODO: We should use the standard library verion of this, if exists.
def rev {α: Type} (l: List α) : List α :=
    match l with
    | [] => []
    | head :: tail => append (rev tail) head
