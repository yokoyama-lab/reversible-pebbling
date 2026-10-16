import SplitLemmaRev
set_option autoImplicit false
namespace SplitLemma
open Finset
example (Y : Finset ℕ) : Dtriv 2 {2} ∅ Y = Dtriv 2 {2} Y ∅ := rfl
end SplitLemma
