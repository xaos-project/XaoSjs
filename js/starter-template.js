function fullScreenMessageToggle(){
    if(fullScreenButton.style.visibility == "collapse"){
        fullScreenButton.style.visibility = "visible";
        resetButton.style.visibility = "visible";
        containerCanvas.style.filter = "blur(5px)";
        fullScreenToggleButton.value = "X";
    }
    else{
        fullScreenButton.style.visibility = "collapse";
        resetButton.style.visibility = "collapse";
        containerCanvas.style.filter = "none";
        fullScreenToggleButton.value = "<";
    }
}

function fullScreenCanvas(){
    canvas.style.visibility = "visible";
    if(canvas.requestFullScreen)    
        canvas.requestFullScreen();
    else if(canvas.webkitRequestFullScreen)
        canvas.webkitRequestFullScreen();
    else if(canvas.mozRequestFullScreen)
        canvas.mozRequestFullScreen();
}