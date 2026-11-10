@echo off
chcp 65001 >nul
cd /d "%~dp0"
py "批量文件水印工具.py"
if errorlevel 1 (
    echo.
    echo 程序启动失败，请先运行“安装依赖.bat”。
    pause
)
