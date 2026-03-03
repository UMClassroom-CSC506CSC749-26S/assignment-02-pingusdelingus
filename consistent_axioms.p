
% Checking upload ... % Checker ran ... % No errors ...

% START OF SYSTEM OUTPUT
% [INFO] 	 Parsing problem /tmp/AnzJIxb9zh/SOT_j50nMc ... 
% [INFO] 	 Parsing done (148ms). 
% SZS status Success for /tmp/AnzJIxb9zh/SOT_j50nMc : Type check succeeded

% END OF SYSTEM OUTPUT
% RESULT: SOT_j50nMc - Leo-III-STC---1.7.20 says Success - CPU = 1.97 WC = 1.00 
% OUTPUT: SOT_j50nMc - Leo-III-STC---1.7.20 says Assurance - CPU = 1.97 WC = 1.00 


tff(species_type, type, species: $tType).
tff(foodlink_type, type, foodlink: $tType).
tff(foodchain_type, type, foodchain: $tType).

tff(eats_decl, type, eats: (species * species) > $o).
tff(eater_decl, type, eater: foodlink > species).
tff(eaten_decl, type, eaten: foodlink > species).

tff(primary_producer_decl, type, primary_producer: species > $o).
tff(apex_predator_decl, type, apex_predator: species > $o).

tff(start_of_decl, type, start_of: foodchain > species).
tff(end_of_decl, type, end_of: foodchain > species).
tff(complete_foodchain_decl, type, complete_foodchain: foodchain > $o).

tff(depends_decl, type, depends: (species * species) > $o).

% AXIOMS

% If one species eats another, there is a food link from the eaten to the eater.
tff(eats_implies_link, axiom, 
    ! [S1: species, S2: species] : 
        ( eats(S1, S2) => 
          ? [L: foodlink] : (eater(L) = S1 & eaten(L) = S2) )
).

% The eater of a food link eats the eaten of the link.
tff(eater_eats_eaten, axiom, 
    ! [L: foodlink] : eats(eater(L), eaten(L))
).

% The eaten and eater of a food link are not the same (no cannibalism).
tff(no_cannibalism, axiom, 
    ! [L: foodlink] : eater(L) != eaten(L)
).

% Every species eats something or is eaten by something (or both).
tff(eater_or_eaten, axiom, 
    ! [S: species] : ( (? [S2: species] : eats(S, S2)) | (? [S3: species] : eats(S3, S)) )
).

% Something is a primary producer iff it eats no other species.
tff(primary_producer_def, axiom, 
    ! [S: species] : ( primary_producer(S) <=> ~ (? [S2: species] : eats(S, S2)) )
).

% Something is an apex predator iff there is no species that eats it.
tff(apex_predator_def, axiom, 
    ! [S: species] : ( apex_predator(S) <=> ~ (? [S2: species] : eats(S2, S)) )
).

% For every food chain, the start of the chain is the eaten of some food link, and one of the following holds... (xor logic using <~>)
tff(foodchain_structure, axiom, 
    ! [C: foodchain] : ? [L: foodlink] : 
        ( start_of(C) = eaten(L) & 
          ( (eater(L) = end_of(C)) <~> 
            (? [C2: foodchain] : (start_of(C2) = eater(L) & end_of(C2) = end_of(C))) 
          ) 
        )
).

% There is no food chain from a species back to itself (no death spirals).
tff(no_death_spirals, axiom, 
    ! [C: foodchain] : start_of(C) != end_of(C)
).

% A complete food chain starts at a primary producer, and ends at an apex predator.
tff(complete_foodchain_def, axiom, 
    ! [C: foodchain] : ( complete_foodchain(C) => (primary_producer(start_of(C)) & apex_predator(end_of(C))) )
).

% Every species is in some complete food chain...
tff(all_species_in_complete_foodchain, axiom, 
    ! [S: species] : ? [C: foodchain] : 
        ( complete_foodchain(C) & 
          ( ( S = start_of(C) & primary_producer(S) ) | 
            ( S = end_of(C) & apex_predator(S) ) | 
            ( ? [C1: foodchain, C2: foodchain] : 
              ( ~complete_foodchain(C1) & start_of(C1) = start_of(C) & end_of(C1) = S & 
                ~complete_foodchain(C2) & start_of(C2) = S & end_of(C2) = end_of(C) ) 
            ) 
          ) 
        )
).

% Given two species, the first depends on the second iff there is a food chain from the second to the first.
tff(depends_def, axiom, 
    ! [S1: species, S2: species] : 
        ( depends(S1, S2) <=> ? [C: foodchain] : (start_of(C) = S2 & end_of(C) = S1) )
).

