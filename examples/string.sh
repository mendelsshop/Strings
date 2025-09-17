for file in *.ml|hs
do
  mv "$file" "${file%.*}.strings"
done

