/-
Copyright (c) 2026 Alex Chengyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hamilton.Infrastructure.CardFin2



namespace Hamilton.Infrastructure

namespace NC

/-- Every NC of `Fin 2` is either `bot` or `top`. -/
theorem nc_fin_two_eq_bot_or_top (π : NC (Finset.univ : Finset (Fin 2))) :
    π = bot _ ∨ π = top (fin_univ_succ_nonempty 1) := by
  have h_lo : 1 ≤ numBlocks π :=
    one_le_numBlocks π (fin_univ_succ_nonempty 1)
  have h_hi : numBlocks π ≤ 2 := nc_numBlocks_le_two π
  have h_eq : numBlocks π = 1 ∨ numBlocks π = 2 := by omega
  rcases h_eq with h1 | h2
  · right; exact nc_with_one_block_eq_top _ π h1
  · left; exact nc_with_two_blocks_eq_bot π h2

/-- `|NC(Fin 2)| = 2`. -/
theorem card_NC_univ_fin_two :
    Fintype.card (NC (Finset.univ : Finset (Fin 2))) = 2 := by
  rw [Fintype.card]
  -- Show Finset.univ : Finset (NC(Fin 2)) = {bot, top}.
  have h_univ : (Finset.univ : Finset (NC (Finset.univ : Finset (Fin 2)))) =
      {bot _, top (fin_univ_succ_nonempty 1)} := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact nc_fin_two_eq_bot_or_top π
  rw [h_univ]
  rw [Finset.card_pair bot_ne_top_fin_two]

/-- `|NC(Fin 2)| = catalan 2`. -/
theorem card_NC_univ_fin_two_eq_catalan :
    Fintype.card (NC (Finset.univ : Finset (Fin 2))) = catalan 2 := by
  rw [card_NC_univ_fin_two, catalan_two]

end NC

end Hamilton.Infrastructure
