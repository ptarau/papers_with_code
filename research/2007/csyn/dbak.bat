zip -9 -ll -r csyn_%1.zip *.pro *.bat *.txt
zip -9 -r csyn_%1.zip *.sln *.vjsproj *.user
copy csyn_%1.zip bak
del /Q csyn_%1.zip
dir bak\csyn_*.zip
