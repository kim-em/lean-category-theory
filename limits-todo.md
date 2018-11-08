Hi @**Reid Barton**, I'm wondering what people want next from limits. Here's my guess:
1. show `forget : Ring ⥤ Type` creates limits and filtered colimits, by hand
2. define adjunctions
3. define reflective subcategories
4. show `forget : CommRing ⥤ Ring` is a reflective subcategory
5. obtain 

Well, `CommRing` is a reflective subcategory of `Ring` (this just means the inclusion has a left adjoint), and this tells us that limits in CommRing are just the limits in Ring.