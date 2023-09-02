# Simplicial-Complexes
a library about Simplicial Complexes in Lean 4 language

We take the part of the code of the auxiliary theorem `lemma subset_of_edges` from Clara L¨oh's Notes about Abstract Simplicial Complex https://loeh.app.uni-regensburg.de/mapa/main.pdf

Todo : 
- importing part of Clara Loh's code to Lean 4

    -[] Euler characteristic
    
    -[] simplicial homology

## Definitions and Theorems
- Simplex
  - dimension

  (example 1, simplex and dimension)
    
  - face
  - proper_face

  (example 2, faces)

  **theorems**
  - dimension of a face is $\le$ dimension of simplex
  - dimension of a proper face is $\lt$ dimension of simplex
  - \# of faces of an n-dim simplex is $2^{(n+1)}$
  - \# of faces of dimesion i of an n-dim simplex is $(^{n+1}_{i+1})$
 
- (Abstract) Simplicial Complex

  (example 3, realline)
  
  - simplex viewed as complex
  - n skeleton
  - simple graph corresponding to 1 skeleton of a complex
 
  **theorems**
  - 1 skeleton of a simplex (viewed as complex) is a clique
 
- maximal element in a simplicial complex
- free face of a simplicial complex

  (example 4, maximal element and free face in realline)

  **theorems**
  - If a free face K exists and M is the corresponding maximal element, dim K = dim M - 1
     

## Acknowledgement

Thanks Clara L¨oh for the note

Thanks to my supervisor Suraj

Thanks to my teammates Ray ZHan, Ziqi Wang, Jiao Huang, Yui Dai 
