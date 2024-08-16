if [ "$#" -eq  "0" ]
then
        echo "Provide the path to scan"
        exit 1;
fi
targetdir=$1

grep -ri --exclude-dir=.git 'butter\|financial\|exchange\|stock\|market\|trading\|GCPTP\|CME\|bubble\|coarse-grained equalization\|CGE\|coarse\|broadcom\|brcm\|brixia\|taygeta\|helga\| ada \|tauri\|buzznik\|guitar\|planetclub\|sfe \|pictor\|sponge\|Orion ' $1 | grep -v 'SymbolicMetadata' | grep -v 'TrafficGenerator'

if [ $? -eq 0 ]
then
        echo "Found Invalid Keys. Pl. check and fix it"
else
        echo "Keyword check Passed."
fi

