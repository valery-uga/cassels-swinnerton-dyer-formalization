import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedFamily
import Mathlib.AlgebraicGeometry.Morphisms.Separated
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonical_incidence_seed_closed
    {K E : Type u} [Field K] [Field E] {B X P Z : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (x : X ⟶ Spec (.of K))
    (p : P ⟶ Spec (.of K)) [IsSeparated p]
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (t : Spec (.of K) ⟶ P) (ht : t ≫ p = 𝟙 _)
    (c : Spec (.of E) ⟶ B) (hc : IsClosed {c (IsLocalRing.closedPoint E)})
    (s : Spec (.of E) ⟶ serreThreePointSectionIncidence b x p marked hm zero)
    (hsP : s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero = c ≫ b ≫ t)
    (hsB : s ≫ serreThreePointSectionIncidenceToConfiguration b x p marked hm zero = c) :
    IsClosed {s (IsLocalRing.closedPoint E)} := by
  let graph : B ⟶ pullback b p :=
    pullback.lift (𝟙 B) (b ≫ t) (by simp only [Category.id_comp, Category.assoc, ht, Category.comp_id])
  have hgraph : graph ≫ pullback.fst b p = 𝟙 _ := pullback.lift_fst _ _ _
  letI : IsClosedImmersion (graph ≫ pullback.fst b p) := by rw [hgraph]; infer_instance
  letI : IsClosedImmersion graph := IsClosedImmersion.of_comp graph (pullback.fst b p)
  let j := serreThreePointSectionIncidenceToProduct b x p marked hm zero
  have he : s ≫ j = c ≫ graph := by
    apply pullback.hom_ext
    · change s ≫ j ≫ pullback.fst b p = (c ≫ graph) ≫ pullback.fst b p
      rw [Category.assoc, hgraph, Category.comp_id]
      exact hsB
    · change s ≫ j ≫ pullback.snd b p = (c ≫ graph) ≫ pullback.snd b p
      rw [Category.assoc, pullback.lift_snd]
      exact hsP
  have hclosed : IsClosed {j (s (IsLocalRing.closedPoint E))} := by
    have h := graph.isClosedMap _ hc
    simp only [Set.image_singleton] at h
    have hpt := congrArg (fun q => q (IsLocalRing.closedPoint E)) he
    exact hpt.symm ▸ h
  have hp := hclosed.preimage j.continuous
  convert hp using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact j.isClosedEmbedding.injective.eq_iff.symm
end PfaffianDescent
