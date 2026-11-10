@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo 正在安装批量文件水印工具所需依赖……
py -m pip install --upgrade pip
py -m pip install -r requirements.txt
if errorlevel 1 (
    echo.
    echo 安装失败。请确认已安装 Python 3.10 或更高版本，并且 py 命令可用。
    pause
    exit /b 1
)
echo.
echo 依赖安装完成。
pause
