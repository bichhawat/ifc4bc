mkdir 2>NUL "%CONFIGURATIONBUILDDIR%\bin"

if exist "%WEBKITLIBRARIESDIR%\bin\CoreFoundation%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\CoreFoundation%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\CoreFoundation%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\CoreFoundation%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\CFNetwork%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\CFNetwork%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\CFNetwork%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\CFNetwork%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\CFNetwork.resources" xcopy /y /d /e /i "%WEBKITLIBRARIESDIR%\bin\CFNetwork.resources" "%CONFIGURATIONBUILDDIR%\bin\CFNetwork.resources"
if exist "%WEBKITLIBRARIESDIR%\bin\CoreFoundation.resources" xcopy /y /d /e /i "%WEBKITLIBRARIESDIR%\bin\CoreFoundation.resources" "%CONFIGURATIONBUILDDIR%\bin\CoreFoundation.resources"
if exist "%WEBKITLIBRARIESDIR%\bin\CoreGraphics%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\CoreGraphics%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\CoreGraphics%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\CoreGraphics%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\icuin40%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\icuin40%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\icuin40%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\icuin40%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\icuuc40%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\icuuc40%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\icuuc40%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\icuuc40%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\libxml2%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\libxml2%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\libxslt%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\libxslt%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\pthreadVC2%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\pthreadVC2%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\pthreadVC2%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\pthreadVC2%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\SQLite3%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\SQLite3%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\SQLite3%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\SQLite3%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\zlib1%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\zlib1%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\zlib1%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\zlib1%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\objc%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\objc%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\objc%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\objc%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"

if exist "%WEBKITLIBRARIESDIR%\bin\QuartzCore%LIBRARYCONFIGSUFFIX%.dll" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\QuartzCore%LIBRARYCONFIGSUFFIX%.dll" "%CONFIGURATIONBUILDDIR%\bin"
if exist "%WEBKITLIBRARIESDIR%\bin\QuartzCore%LIBRARYCONFIGSUFFIX%.pdb" xcopy /y /d "%WEBKITLIBRARIESDIR%\bin\QuartzCore%LIBRARYCONFIGSUFFIX%.pdb" "%CONFIGURATIONBUILDDIR%\bin"

if exist "%CONFIGURATIONBUILDDIR%\buildfailed" del "%CONFIGURATIONBUILDDIR%\buildfailed"
