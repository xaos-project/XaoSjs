function captureMenu(){
    if(browseButton.style.visibility == "collapse"){
        browseButton.style.visibility = "visible";
        resetButton.style.visibility = "visible";
        saveCanvasButton.style.visibility = "collapse";
        instructions.style.visibility = "visible";
        containerCanvas.style.filter = "blur(5px)";
        captureMenuButton.value = "Capture Mode";
    }
    else{
        browseButton.style.visibility = "collapse";
        resetButton.style.visibility = "collapse";
        saveCanvasButton.style.visibility = "visible";
        instructions.style.visibility = "collapse";
        containerCanvas.style.filter = "none";
        captureMenuButton.value = "Go Back";
    }
}

function browseMenu(){    
    if(canvas.requestFullScreen)    
        canvas.requestFullScreen();
    else if(canvas.webkitRequestFullScreen)
        canvas.webkitRequestFullScreen();
    else if(canvas.mozRequestFullScreen)
        canvas.mozRequestFullScreen();
}

function saveCanvas(){
    saveCanvasButton.download = "image.png";
    saveCanvasButton.href = canvas.toDataURL("image/png").replace("image/png", "image/octet-stream");
}