import PfaffianDescent.IncidenceTotalSpaceLocal
import PfaffianDescent.IncidenceQuotientCharts

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

lemma openAffineFunctionHom_homOfLE (U V : X.Opens) (h : V ≤ U)
    (f : U.toScheme ⟶ Spec (.of R)) :
    openAffineFunctionHom V (X.homOfLE h ≫ f) =
      (regularFunctionRestrictFrom X U V h).comp (openAffineFunctionHom U f) := by
  have he := openAffineFunctionHom_resLE (𝟙 X) U V h f
  rw [Scheme.Hom.resLE_id] at he
  have ha : (Scheme.Hom.appLE (𝟙 X) U V h).hom = regularFunctionRestrictFrom X U V h := by
    change (Scheme.Hom.app (𝟙 X) U ≫ X.presheaf.map (homOfLE h).op).hom = _
    rw [Scheme.Hom.id_app]
    rfl
  rw [ha] at he
  exact he

end
section
variable (K : Type u) [CommRing K]

/-- The actual ambient alternating-form coefficients of a scheme section. -/
noncomputable def incidenceSchemeSectionCoefficients
    (U : (grassmannianScheme K 3 3).Opens) (s : IncidenceSchemeSections K U) :
    AlternatingTripleIndex → Γ(grassmannianScheme K 3 3, U) :=
  fun i => openAffineFunctionHom U (s.1 ≫ incidenceToTriples K) (MvPolynomial.X i)

lemma incidenceSchemeSectionCoefficients_injective
    (U : (grassmannianScheme K 3 3).Opens) :
    Function.Injective (incidenceSchemeSectionCoefficients K U) := by
  intro s t h
  apply Subtype.ext
  apply incidence_hom_ext K s.1 t.1 (s.2.trans t.2.symm)
  apply alternatingTriple_morphism_ext K
  · rw [Category.assoc, Category.assoc, incidenceToTriples_toBase, ← incidenceToGrassmannian_toBase,
      ← Category.assoc, ← Category.assoc, s.2, t.2]
  · intro i
    apply U.topIso.commRingCatIsoToRingEquiv.injective
    exact congrFun h i

lemma incidenceSchemeSectionCoefficients_restrict
    (U V : (grassmannianScheme K 3 3).Opens) (h : V ≤ U) (s : IncidenceSchemeSections K U) :
    incidenceSchemeSectionCoefficients K V (incidenceSchemeSectionsRestrict K U V h s) =
      regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V h ∘ incidenceSchemeSectionCoefficients K U s := by
  funext i
  change openAffineFunctionHom V (((grassmannianScheme K 3 3).homOfLE h ≫ s.1) ≫ incidenceToTriples K)
    (MvPolynomial.X i) = _
  exact (congrArg (fun f => openAffineFunctionHom V f (MvPolynomial.X i))
    (Category.assoc ((grassmannianScheme K 3 3).homOfLE h) s.1 (incidenceToTriples K))).trans
      (RingHom.congr_fun (openAffineFunctionHom_homOfLE U V h (s.1 ≫ incidenceToTriples K)) (MvPolynomial.X i))

end
end PfaffianDescent
