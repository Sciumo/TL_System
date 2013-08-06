@echo off

REM If you want to be able to run ZGRViewer from any directory,
REM set ZGRV to the absolute path of ZGRViewer's main directory
REM e.g. SET ZGRV=C:\tools\zgrviewer

SET ZGRV=%~p0
REM SET ZGRV="C:\Users\vwinter\UNO-Research\Project - Library Migration\Documents\Dot Language\zgrviewer"

start java -jar "%ZGRV%\target\zgrviewer-0.8.2.jar" %1 %2 %3 %4
