import PfaffianDescent.GrassmannianSmooth

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- Finitely many affine graph charts cover the Grassmannian scheme. -/
instance grassmannianScheme_compactSpace (m n : ℕ) : CompactSpace (grassmannianScheme K m n) := by
  let 𝒰 := (grassmannianGlueData K m n).openCover
  letI : Finite 𝒰.I₀ := inferInstanceAs (Finite (ULift.{u} (Equiv.Perm (Fin m ⊕ Fin n))))
  letI (i : 𝒰.I₀) : CompactSpace (𝒰.X i) :=
    inferInstanceAs (CompactSpace (Spec (.of (GrassmannianChartRing K m n))))
  exact 𝒰.compactSpace

instance grassmannianToBase_quasiCompact (m n : ℕ) : QuasiCompact (grassmannianToBase K m n) := by
  exact quasiCompact_of_compactSpace (grassmannianToBase K m n)

instance grassmannianToBase_locallyOfFiniteType (m n : ℕ) : LocallyOfFiniteType (grassmannianToBase K m n) :=
  inferInstance

end
section
variable (K : Type u) [CommRing K] [IsNoetherianRing K]

instance grassmannianScheme_isLocallyNoetherian (m n : ℕ) :
    IsLocallyNoetherian (grassmannianScheme K m n) :=
  LocallyOfFiniteType.isLocallyNoetherian (grassmannianToBase K m n)

instance grassmannianScheme_isNoetherian (m n : ℕ) : IsNoetherian (grassmannianScheme K m n) :=
  ⟨⟩

instance grassmannianToBase_quasiSeparated (m n : ℕ) : QuasiSeparated (grassmannianToBase K m n) :=
  QuasiSeparated.of_quasiSeparatedSpace (grassmannianToBase K m n)

end
end PfaffianDescent
