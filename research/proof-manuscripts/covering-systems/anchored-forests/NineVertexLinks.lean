import Std

/-! The tripartite complement of the nine-cycle in Baber–Johnson–Talbot, Figure 1.
    Labels in each part start at zero. -/
namespace NineVertexLinks

def tri (a b c : Fin 3) : Prop :=
  a ≠ b ∧ a ≠ c ∧ c.val ≠ (b.val+1)%3

theorem links_hit_every_triangle : ∀ a b c i j k : Fin 3,
    tri a b c → tri i j k ∨ tri i b c ∨ tri a j c ∨ tri a b k := by
  unfold tri
  decide

#print axioms links_hit_every_triangle
end NineVertexLinks
