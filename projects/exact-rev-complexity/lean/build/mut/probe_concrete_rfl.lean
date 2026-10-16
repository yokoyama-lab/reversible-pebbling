import SplitLemmaRev
set_option autoImplicit false
namespace SplitLemma
open Finset
example : Dtriv 2 {2} ∅ ({2} : Finset ℕ) = Dtriv 2 {2} ({2} : Finset ℕ) ∅ := rfl
end SplitLemma
