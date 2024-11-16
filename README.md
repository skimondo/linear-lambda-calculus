# Lambda Linear Logic: Beluga and Coq Implementations

The purpose of this repository it to translate an implementation of the lambda linear logic from beluga proof assistant to coq proof assistant.
An implementation using CARVe method in Beluga proof assistant is available [here](https://zenodo.org/records/13777002).

the [beluga directory](beluga/README.md) in this repository is a minimal set of definitions and lemmas from the original implementation to focus on the linear logic aspect of the project.

## Project Goals

1. **Translation into coq**: Translating all the definitions and lemmas from Beluga to Coq.
2. **Implementation Comparison**: Show the contrast between the two proof assistants in terms of proof complexity, implementation challenges, and overall ease of use. see [comparison.md](docs/comparison.md)
3. **Documentation and Analysis**: Provide documentation on the implementation process, challenges faced, and lessons learned.

## Repository Structure (Abreviated)

```plaintext
.
├── README.md                 
├── beluga/                          
│   ├── common/
│   │   ├── defs 
│   │   └── lemmas  
│   └── run_all.cfg
├── coq/                      
│   ├── _CoqProject           
│   ├── common/
│   │   ├── defs 
│   │   └── lemmas  
└── docs/                     
    └── comparison.md         
```
