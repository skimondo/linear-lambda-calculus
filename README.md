# Lambda Linear Logic: Beluga and Coq Implementations

The purpose of this repository it to implement the lambda linear logic using coq proof assistant.
An implementattion is already available using Beluga proof assistant inside [carve directory](carve/README.md), it was written by Anonymous Author(s).

## Project Goals

1. **Translation into coq**: Translating all the definitions, lemmas, and theorems from Beluga to Coq.
2. **Implementation Comparison**: Show the contrast between the two proof assistants in terms of proof complexity, implementation challenges, and overall ease of use. see [comparison.md](docs/comparison.md)
3. **Documentation and Analysis**: Provide documentation on the implementation process, challenges faced, and lessons learned.

## Repository Structure (Under Construction)

```plaintext
linear-lambda-calculus
├── README.md                 
├── carve/                    
│   ├── case_studies/         
│   ├── common/               
│   └── run_all.cfg
├── coq/                      
│   ├── _CoqProject           
│   ├── Makefile              
│   ├── case_studies/
│   └── common/
└── docs/                     
    ├── comparison.md         
    └── setup_instructions.md 
