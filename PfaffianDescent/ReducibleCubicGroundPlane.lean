import PfaffianDescent.LinearFactorPoint
import PfaffianDescent.HomogeneousQuotientMap

/-! A reducible nonzero homogeneous cubic over its arbitrary coefficient field
has a homogeneous linear factor over that same field. Its literal ground
plane V(ℓ) is a closed subscheme of the same original cubic, with the
canonical ambient P³ map unchanged, and gives a section through that plane. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
universe u v

section Algebra
variable {k : Type u} {σ : Type v} [Field k]

/-- Reducibility and total degree three give a genuine ground factorization
into nonzero homogeneous factors of degrees one and two. -/
theorem reducible_homogeneous_cubic_linear_quadratic_factor
    (F : MvPolynomial σ k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    (hred : ¬ Irreducible F) :
    ∃ ℓ Q : MvPolynomial σ k, ℓ ≠ 0 ∧ Q ≠ 0 ∧
      ℓ.IsHomogeneous 1 ∧ Q.IsHomogeneous 2 ∧ F = ℓ * Q := by
  have hunit : ¬ IsUnit F :=
    homogeneous_not_isUnit_of_pos_degree_of_eval_zero hF (by decide)
  obtain hirr | ⟨a, b, hau, hbu, hfactor⟩ := irreducible_or_factor hunit
  · exact False.elim (hred hirr)
  have ha₀ : a ≠ 0 := by
    intro ha
    apply hF₀
    rw [hfactor, ha, zero_mul]
  have hb₀ : b ≠ 0 := by
    intro hb
    apply hF₀
    rw [hfactor, hb, mul_zero]
  have hdegree : a.totalDegree + b.totalDegree = 3 := by
    rw [← totalDegree_mul_of_isDomain ha₀ hb₀, ← hfactor]
    exact hF.totalDegree hF₀
  have hapos : 0 < a.totalDegree := totalDegree_pos_of_nonunit ha₀ hau
  have hbpos : 0 < b.totalDegree := totalDegree_pos_of_nonunit hb₀ hbu
  obtain ⟨ha, hb⟩ := homogeneous_factor_of_homogeneous_product ha₀ hb₀ (hfactor ▸ hF)
  by_cases haone : a.totalDegree = 1
  · have hbtwo : b.totalDegree = 2 := by omega
    exact ⟨a, b, ha₀, hb₀, haone ▸ ha, hbtwo ▸ hb, hfactor⟩
  · have hbone : b.totalDegree = 1 := by omega
    have hatwo : a.totalDegree = 2 := by omega
    exact ⟨b, a, hb₀, ha₀, hbone ▸ hb, hatwo ▸ ha, hfactor.trans (mul_comm a b)⟩

/-- The original reducible cubic has a nonzero homogeneous ground linear divisor. -/
theorem reducible_homogeneous_cubic_linear_divisor
    (F : MvPolynomial σ k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    (hred : ¬ Irreducible F) :
    ∃ ℓ : MvPolynomial σ k, ℓ ≠ 0 ∧ ℓ.IsHomogeneous 1 ∧ ℓ ∣ F := by
  obtain ⟨ℓ, Q, hℓ₀, hQ₀, hℓ, hQ, hfactor⟩ :=
    reducible_homogeneous_cubic_linear_quadratic_factor F hF hF₀ hred
  exact ⟨ℓ, hℓ₀, hℓ, Q, hfactor⟩

end Algebra

section Geometry
open AlgebraicGeometry CategoryTheory AllCharacteristics.HomogeneousProjective
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal V(ℓ) ground plane embeds into the SAME original cubic and
has a ground section. Both the canonical P³ embedding and coefficient
structure map are respected by the constructed closed immersion. -/
theorem reducible_homogeneous_cubic_contains_ground_plane_and_section
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    (hred : ¬ Irreducible F) :
    ∃ ℓ : MvPolynomial (Fin 4) k, ∃ hℓ : ℓ.IsHomogeneous 1,
      ℓ ≠ 0 ∧ ℓ ∣ F ∧
      ∃ i : hypersurface ℓ hℓ ⟶ hypersurface F hF,
        IsClosedImmersion i ∧
        i ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap (equationIdeal ℓ hℓ) ∧
        i ≫ hypersurfaceToBase F hF = hypersurfaceToBase ℓ hℓ ∧
        ∃ t : Spec (.of k) ⟶ hypersurface ℓ hℓ,
          t ≫ hypersurfaceToBase ℓ hℓ = 𝟙 _ ∧
          (t ≫ i) ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨ℓ, hℓ₀, hℓ, hdiv⟩ := reducible_homogeneous_cubic_linear_divisor F hF hF₀ hred
  let I := equationIdeal F hF
  let J := equationIdeal ℓ hℓ
  have hIJ : I.toIdeal ≤ J.toIdeal := by
    change Ideal.span ({F} : Set (MvPolynomial (Fin 4) k)) ≤
      Ideal.span ({ℓ} : Set (MvPolynomial (Fin 4) k))
    apply Ideal.span_le.mpr
    intro p hp
    obtain rfl := Set.mem_singleton_iff.mp hp
    exact Ideal.mem_span_singleton.mpr hdiv
  let i : hypersurface ℓ hℓ ⟶ hypersurface F hF := schemeQuotientMap I J hIJ
  have hi : IsClosedImmersion i := schemeQuotientMap_closedImmersion I J hIJ
  have hambient : i ≫ quotientProjMap I = quotientProjMap J :=
    schemeQuotientMap_comp_quotientProjMap I J hIJ
  have hbase : i ≫ hypersurfaceToBase F hF = hypersurfaceToBase ℓ hℓ :=
    schemeQuotientMap_toBase I J hIJ
  obtain ⟨x, hx, hℓx⟩ := homogeneous_linear_has_nonzero_zero ℓ hℓ (by decide : 1 < 4)
  obtain ⟨t, ht⟩ := hypersurface_point_of_coordinates (RingHom.id k) ℓ hℓ x hx hℓx
  have htbase : t ≫ hypersurfaceToBase ℓ hℓ = 𝟙 _ := by simpa using ht
  have hsection : (t ≫ i) ≫ hypersurfaceToBase F hF = 𝟙 _ :=
    (Category.assoc t i (hypersurfaceToBase F hF)).trans
      ((congrArg (fun g => t ≫ g) hbase).trans htbase)
  exact ⟨ℓ, hℓ, hℓ₀, hdiv, i, hi, hambient, hbase, t, htbase, hsection⟩

/-- The ground-plane section gives a section of the SAME original reducible cubic. -/
theorem reducible_homogeneous_cubic_has_ground_section
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    (hred : ¬ Irreducible F) :
    ∃ s : Spec (.of k) ⟶ hypersurface F hF, s ≫ hypersurfaceToBase F hF = 𝟙 _ := by
  obtain ⟨ℓ, hℓ, hℓ₀, hdiv, i, hi, hambient, hbase, t, ht, hsection⟩ :=
    reducible_homogeneous_cubic_contains_ground_plane_and_section F hF hF₀ hred
  exact ⟨t ≫ i, hsection⟩

end Geometry
end PfaffianDescent
