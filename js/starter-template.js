function saveCanvas(){
    saveCanvasButton.download = "image.png";
    saveCanvasButton.href = canvas.toDataURL("image/png").replace("image/png", "image/octet-stream");
  }
  function goFullScreen() {
    if(canvas.requestFullScreen)    
    canvas.requestFullScreen();
    else if(canvas.webkitRequestFullScreen)
        canvas.webkitRequestFullScreen();
    else if(canvas.mozRequestFullScreen)
        canvas.mozRequestFullScreen();
  }
