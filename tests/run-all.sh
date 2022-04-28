stat ../cleaner > /dev/null 2> /dev/null
if [ ! "$?" -eq "0" ];
then
    pushd
    cd ..
    make
    popd
    stat ../cleaner > /dev/null 2> /dev/null
    if [ ! "$?" -eq "0" ];
    then
        echo "Hook cleaner not found in parent directory, build attempt failed."
        exit 1
    fi
fi

which wasm2wat > /dev/null 2> /dev/null
if [ ! "$?" -eq "0" ];
then
    echo "wasm2wat not found, please install wabt"
    exit 2
fi

PASSED=0
COUNT=0
TOTALSAVED=0
for i in `ls *.wasm`; do
    COUNT=`expr $COUNT + 1`
    rm /tmp/t.wasm
    ../cleaner $i /tmp/t.wasm > /dev/null 2> /dev/null
    R1="$?"
    wasm2wat /tmp/t.wasm > /dev/null 2> /dev/null
    R2="$?"

    FN="`echo $i | grep -Eo '^[^\.]+'`"
    if [ $R1 -eq "0" ];
    then
        if [ $R2 -eq "0" ];
        then
            BEFORE="`du -b $i | grep -Eo '^[0-9]+'`"
            AFTER="`du -b /tmp/t.wasm | grep -Eo '^[0-9]+'`"
            SAVED="`expr $BEFORE - $AFTER`"
            echo -e "TEST $COUNT -- $FN \t-- PASS (-$SAVED b)"
            TOTALSAVED="`expr $TOTALSAVED + $SAVED`"
            PASSED="`expr $PASSED + 1`"
        else
            echo -e "TEST $COUNT -- $FN \t-- FAIL wasm2wat"
        fi
    else
        echo -e "TEST $COUNT -- $FN \t-- FAIL"
    fi
done

if [ "$PASSED" -eq "$COUNT" ];
then
    echo "All tests passed! Average bytes saved: `expr $TOTALSAVED / $COUNT` b"
else
    echo "NOT All tests passed: `expr $COUNT - $PASSED` failed."
fi

