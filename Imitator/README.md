To run the benchmarks, first install Docker.

Then install Imitator by running the following command:

    docker install imitator/imitator

To run the benchmarks, open a terminal in PTAs and use below commands. Not halting ones are commented. 
For Windows terminal, replace "./" with "%cd%" in mount directory.
For Windows PowerShell, replace "./" with "${PWD}" in mount directory.

If the command line arguments to a Docker container is forgotten, use the below command to retrieve them:

    docker inspect -f '{{ .Config.Cmd}}' container_id

Safety Benchmarks:

    docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/BlT09_fig1.imi /mnt/ptas/BlT09_fig1-AGnot.imiprop
    docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Cycles_2.imi /mnt/ptas/Cycles_2-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Cycles_5_6.imi /mnt/ptas/Cycles_5_6-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Cycles_notFiniteDisjunction.imi /mnt/ptas/Cycles_notFiniteDisjunction-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/JLR15_Fig6.imi /mnt/ptas/JLR15_Fig6-AGnot.imiprop
    docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/NuclearPlant.imi /mnt/ptas/NuclearPlant-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/PTAfromFig1.imi /mnt/ptas/PTAfromFig1-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Synth_3N.imi /mnt/ptas/Synth_3N-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Synth_int01.imi /mnt/ptas/Synth_int01-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Synth_InvN.imi /mnt/ptas/Synth_InvN-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Synth_N.imi /mnt/ptas/Synth_N-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Synth_pN.imi /mnt/ptas/Synth_pN-AGnot.imiprop
    # docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Synth_pNplusq.imi /mnt/ptas/Synth_pNplusq-AGnot.imiprop
    docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/Train1PTA.imi /mnt/ptas/Train1PTA-AGnot.imiprop
    docker run -v ./:/mnt/ptas imitator/imitator /mnt/ptas/UntimedLanguage.imi /mnt/ptas/UntimedLanguage-AGnot.imiprop
