# Classification of finite subgroups of $\textrm{PGL}_2(\bar{\mathbb{F}}_p)$


## Content of this project

This project contains the $\LaTeX$ blueprint and the (ongoing) Lean formalization of the classification of finite subgroups of $\textrm{PGL}_2(F)$.

Which states:

- If $H$ is finite subgroup of $\textrm{PGL}\_2(\mathbb{C})$ then $H$ is isomorphic to one of the following groups: the cyclic group $C_n$ of order $n$ ($n \in Z_{>0}$), the dihedral group $D_{2n}$ of order $2n$ ($n \in Z_{>1}$), $A_4$, $S_4$ or $A_5$.
- If $H$ is a finite subgroup of $\textrm{PGL}_2(\bar{F}_p)$ then one of the following holds:
  1. $H$ is conjugate to a subgroup of the upper triangular matrices;
  2. $H$ is conjugate to $\textrm{PGL}\_2 (F_{\ell^r})$ and $\textrm{PSL}\_2 (F\_{\ell^r})$ for some $r \in Z_{>0}$;
  3. $H$ is isomorphic to $A_4$, $S_4$, $A_5$ or the dihedral group $D_{2r}$ of order $2r$ for some $r \in Z_{>1}$ not divisible by $\ell$

Where $\ell$ is assumed to be an odd prime.

## The big picture

This project is a contribution towards the formalization of Fermat's Last Theorem (see https://github.com/ImperialCollegeLondon/FLT), the result formalized covers Theorem 2.47 in [FermatLastTheorem](https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf)

## Acknowledgements

I thank my supervisor Prof. David Jordan for his invaluable support and guidance throughout the project, 

I would also like to thank Christopher Butler for providing the $\LaTeX$ code so I could easily set up the blueprint.

I would also like to thank Prof. Kevin Buzzard for his support and patience.

Finally, I would like to thank the many members of the Lean Zulip community who have provided insightful ideas and comments that have helped me progress much faster than otherwise.

## Contributing

Contributions are welcome! If you would like to contribute, I recommend looking through the reference below and contacting me via zulip so I can find you a suitable task. 
At the time of writing, I am formalising lemma 2.3 iv) b); and hope to be soon formalising the inequality on page 35, which will lead to the case split on the classification of the arbitrary finite group.

## Source reference

`CB` : [ChristopherButlerExpositionOfDicksonsClassificationTheorem](https://lup.lub.lu.se/student-papers/record/8998907/file/8998908.pdf)


